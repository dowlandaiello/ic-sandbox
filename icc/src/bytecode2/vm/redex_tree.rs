use std::{
    cell::Cell,
    collections::{BTreeMap, VecDeque},
    default,
    rc::Rc,
};

/// Can be matched against other stack elems without having to worry about ports,
/// ptrs, etc.
#[derive(Debug, PartialEq, Eq, Ord, PartialOrd)]
pub enum RedexTreeElem {
    Agent { name: String },
    Var(String),
}

#[derive(Debug, Clone)]
pub struct RedexTree<V: Copy> {
    roots: BTreeMap<Rc<RedexTreeElem>, RedexNode<V>>,
}

impl<V: Copy> default::Default for RedexTree<V> {
    fn default() -> Self {
        Self {
            roots: Default::default(),
        }
    }
}

impl<V: Copy> RedexTree<V> {
    pub fn get_inner(&self, tree: impl Iterator<Item = RedexTreeElem>) -> Option<V> {
        self.iter_tree(tree)
            .last()
            .and_then(|elem| elem.value.get())
    }

    pub fn insert(
        &mut self,
        mut tree: impl Iterator<Item = RedexTreeElem>,
        value: V,
    ) -> Option<()> {
        let first_key = Rc::new(tree.next()?);

        self.roots
            .entry(first_key.clone())
            .or_insert(RedexNode::new(first_key, None))
            .insert_tree(tree, value)
    }

    pub fn get(&self, tree: impl Iterator<Item = RedexTreeElem>) -> Option<&Cell<Option<V>>> {
        self.iter_tree(tree).last().map(|elem| &elem.value)
    }

    pub fn contains_key(&self, tree: impl Iterator<Item = RedexTreeElem>) -> bool {
        self.iter_tree(tree).last().is_some()
    }

    fn get_root_mut(&mut self, k: RedexTreeElem) -> Option<&mut RedexNode<V>> {
        self.roots.get_mut(&k)
    }

    fn get_root(&self, k: RedexTreeElem) -> Option<&RedexNode<V>> {
        self.roots.get(&k)
    }

    fn iter_tree(
        &self,
        mut keys: impl Iterator<Item = RedexTreeElem>,
    ) -> impl Iterator<Item = &RedexNode<V>> {
        Iter::new(keys.next().and_then(|k| self.get_root(k)), keys)
    }
}

struct Iter<'a, V: Copy> {
    curr: Option<&'a RedexNode<V>>,
    plan: VecDeque<RedexTreeElem>,
}

impl<'a, V: Copy> Iter<'a, V> {
    fn new(curr: Option<&'a RedexNode<V>>, plan: impl Iterator<Item = RedexTreeElem>) -> Self {
        Self {
            curr,
            plan: plan.collect(),
        }
    }
}

impl<'a, V: Copy> Iterator for Iter<'a, V> {
    type Item = &'a RedexNode<V>;

    fn next(&mut self) -> Option<Self::Item> {
        let curr = self.curr?;
        self.curr = curr.get(&self.plan.pop_front()?);

        Some(curr)
    }
}

#[derive(Debug, Clone)]
struct RedexNode<V: Copy> {
    key: Rc<RedexTreeElem>,
    value: Cell<Option<V>>,
    children: BTreeMap<Rc<RedexTreeElem>, RedexNode<V>>,
}

impl<V: Copy> RedexNode<V> {
    fn new(key: Rc<RedexTreeElem>, value: Option<V>) -> Self {
        Self {
            key,
            children: Default::default(),
            value: value.into(),
        }
    }

    fn insert_tree(
        &mut self,
        mut tree: impl Iterator<Item = RedexTreeElem>,
        value: V,
    ) -> Option<()> {
        if tree.next().is_none() {
            self.value = Cell::new(Some(value));

            return None;
        }

        let next_key = Rc::new(tree.next()?);

        Self::insert_tree(
            self.children
                .entry(next_key.clone())
                .or_insert(RedexNode::new(next_key, None)),
            tree,
            value,
        )
    }

    fn insert(&mut self, k: RedexTreeElem, v: V) -> &mut Self {
        if self.key.as_ref() == &k {
            self.value = Cell::new(Some(v));

            return self;
        }

        let heaped: Rc<RedexTreeElem> = k.into();
        self.children
            .entry(heaped.clone())
            .or_insert_with(|| RedexNode::new(heaped, None))
    }

    fn get(&self, elem: &RedexTreeElem) -> Option<&Self> {
        self.children.get(elem)
    }

    fn get_mut(&mut self, elem: &RedexTreeElem) -> Option<&mut Self> {
        self.children.get_mut(elem)
    }
}
