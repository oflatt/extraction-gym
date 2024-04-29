use std::iter;

use rpds::HashTrieSet;

use super::*;

type TermId = usize;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct Term {
    op: String,
    children: Vec<TermId>,
}

type Reachable = HashTrieSet<ClassId>;

struct TermInfo {
    node: NodeId,
    eclass: ClassId,
    node_cost: Cost,
    total_cost: Cost,
    // store the set of reachable terms from this term
    reachable: Reachable,
    size: usize,
}

/// A TermDag needs to store terms that share common
/// subterms using a hashmap.
/// However, it also critically needs to be able to answer
/// reachability queries in this dag `reachable`.
/// This prevents double-counting costs when
/// computing the cost of a term.
#[derive(Default)]
pub struct TermDag {
    nodes: Vec<Term>,
    info: Vec<TermInfo>,
    hash_cons: HashMap<Term, TermId>,
}

impl TermDag {
    /// Makes a new term using a node and children terms
    /// Correctly computes total_cost with sharing
    /// If this term contains itself, returns None
    /// It can also return None if the cost of the term is greater than target
    pub fn make(
        &mut self,
        node_id: NodeId,
        node: &Node,
        children: Vec<TermId>,
        target: Cost,
    ) -> Option<TermId> {
        let term = Term {
            op: node.op.clone(),
            children: children.clone(),
        };

        if let Some(id) = self.hash_cons.get(&term) {
            eprintln!("Found shared term: {:?}", term);
            eprintln!("Node: {:?}", node);
            return Some(*id);
        }

        let node_cost = node.cost;

        if children.is_empty() {
            let next_id = self.nodes.len();
            self.nodes.push(term.clone());
            self.info.push(TermInfo {
                node: node_id,
                eclass: node.eclass.clone(),
                node_cost,
                total_cost: node_cost,
                reachable: iter::once(node.eclass.clone()).collect(),
                size: 1,
            });
            self.hash_cons.insert(term, next_id);
            Some(next_id)
        } else {
            // check if children contains this node, preventing cycles
            // This is sound because `reachable` is the set of reachable eclasses
            // from this term.
            for child in &children {
                if self.info[*child].reachable.contains(&node.eclass) {
                    return None;
                }
            }

            let biggest_child = (0..children.len())
                .max_by_key(|i| self.info[children[*i]].size)
                .unwrap();

            let mut cost = node_cost + self.total_cost(children[biggest_child]);
            let mut reachable = self.info[children[biggest_child]].reachable.clone();
            let next_id = self.nodes.len();

            for child in children.iter() {
                if cost >= target {
                    return None;
                }
                let child_cost = self.get_cost(&mut reachable, *child);
                cost += child_cost;
            }

            reachable = reachable.insert(node.eclass.clone());

            self.nodes.push(term.clone());
            self.info.push(TermInfo {
                node: node_id,
                node_cost,
                eclass: node.eclass.clone(),
                total_cost: cost,
                reachable,
                size: 1 + children.iter().map(|c| self.info[*c].size).sum::<usize>(),
            });

            self.hash_cons.insert(term, next_id);
            Some(next_id)
        }
    }

    /// Return a new term, like this one but making use of shared terms.
    /// Also return the cost of the new nodes.
    fn get_cost(&self, shared: &mut Reachable, id: TermId) -> Cost {
        let eclass = self.info[id].eclass.clone();

        // This is the key to why this algorithm is faster than greedy_dag.
        // While doing the set union between reachable sets, we can stop early
        // if we find a shared term.
        // Since the term with `id` is shared, the reachable set of `id` will already
        // be in `shared`.
        if shared.contains(&eclass) {
            NotNan::<f64>::new(0.0).unwrap()
        } else {
            let mut cost = self.node_cost(id);
            for child in &self.nodes[id].children {
                let child_cost = self.get_cost(shared, *child);
                cost += child_cost;
            }
            *shared = shared.insert(eclass);
            cost
        }
    }

    pub fn node_cost(&self, id: TermId) -> Cost {
        self.info[id].node_cost
    }

    pub fn total_cost(&self, id: TermId) -> Cost {
        self.info[id].total_cost
    }
}

/// Choose terms from the term dag to form the extraction result.
/// If something has already been chosen, stick to that choice (otherwise, cycles can result).
fn choose_terms(result: &mut ExtractionResult, termdag: &TermDag, term: TermId) {
    let terminfo = &termdag.info[term];
    let term = &termdag.nodes[term];
    let eclass = terminfo.eclass.clone();
    if !result.choices.contains_key(&eclass) {
        result.choose(eclass, terminfo.node.clone());
        for child in &term.children {
            choose_terms(result, termdag, *child);
        }
    }
}

pub struct GlobalGreedyDagExtractor;
impl Extractor for GlobalGreedyDagExtractor {
    fn extract(&self, egraph: &EGraph, roots: &[ClassId]) -> ExtractionResult {
        // 1. build map from class to parent nodes
        let mut parents = IndexMap::<ClassId, Vec<NodeId>>::default();
        let n2c = |nid: &NodeId| egraph.nid_to_cid(nid);

        for class in egraph.classes().values() {
            parents.insert(class.id.clone(), Vec::new());
        }
        for class in egraph.classes().values() {
            for node in &class.nodes {
                for c in &egraph[node].children {
                    parents[n2c(c)].push(node.clone());
                }
            }
        }

        // 2. start analysis from leaves
        let mut analysis_pending = UniqueQueue::default();

        for class in egraph.classes().values() {
            for node in &class.nodes {
                if egraph[node].is_leaf() {
                    analysis_pending.insert(node.clone());
                }
            }
        }

        let nodes = egraph.nodes.clone();
        let mut termdag = TermDag::default();
        let mut best_in_class: HashMap<ClassId, TermId> = HashMap::default();

        while let Some(node_id) = analysis_pending.pop() {
            let node = &nodes[&node_id];
            let class_id = n2c(&node_id);
            let mut children: Vec<TermId> = vec![];
            // compute the cost set from the children
            for child in &node.children {
                let child_cid = egraph.nid_to_cid(child);
                if let Some(best) = best_in_class.get(child_cid) {
                    children.push(*best);
                } else {
                    continue;
                }
            }

            let old_cost = best_in_class
                .get(&node.eclass)
                .map(|id| termdag.total_cost(*id))
                .unwrap_or(INFINITY);

            if let Some(candidate) = termdag.make(node_id.clone(), node, children, old_cost) {
                assert_eq!(termdag.info[candidate].eclass, node.eclass, "eclass mismatch- either a bug in global greedy dag, or the input benchmark doesn't maintain congruence");
                let candidate_cost = termdag.total_cost(candidate);
                if candidate_cost < old_cost {
                    best_in_class.insert(node.eclass.clone(), candidate);
                    analysis_pending.extend(parents[class_id].iter().cloned());
                }
            }
        }

        // TODO this algorithm can result in cycles
        // the problem is that if roots has length greater than zero, then
        // there will be two extracted programs, one for each root.
        // However, we may need to make different choices for eclasses depending on the root,
        // while the extraction gym currently only allows us one.

        let mut result = ExtractionResult::default();
        for root in roots {
            choose_terms(&mut result, &termdag, best_in_class[root]);
        }
        
        result
    }
}

/** A data structure to maintain a queue of unique elements.

Notably, insert/pop operations have O(1) expected amortized runtime complexity.
*/
#[derive(Clone)]
#[cfg_attr(feature = "serde-1", derive(Serialize, Deserialize))]
pub(crate) struct UniqueQueue<T>
where
    T: Eq + std::hash::Hash + Clone,
{
    set: std::collections::HashSet<T>, // hashbrown::
    queue: std::collections::VecDeque<T>,
}

impl<T> Default for UniqueQueue<T>
where
    T: Eq + std::hash::Hash + Clone,
{
    fn default() -> Self {
        UniqueQueue {
            set: std::collections::HashSet::default(),
            queue: std::collections::VecDeque::new(),
        }
    }
}

impl<T> UniqueQueue<T>
where
    T: Eq + std::hash::Hash + Clone,
{
    pub fn insert(&mut self, t: T) {
        if self.set.insert(t.clone()) {
            self.queue.push_back(t);
        }
    }

    pub fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        for t in iter.into_iter() {
            self.insert(t);
        }
    }

    pub fn pop(&mut self) -> Option<T> {
        let res = self.queue.pop_front();
        res.as_ref().map(|t| self.set.remove(t));
        res
    }

    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        let r = self.queue.is_empty();
        debug_assert_eq!(r, self.set.is_empty());
        r
    }
}
