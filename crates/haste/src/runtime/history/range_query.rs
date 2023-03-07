/// A Binary-Indexed-Tree (BIT) which for each index `i` stores the result of applying some
/// function `accumulate` to all values in the range `i..`.
///
/// The implementation is heavily inspired by the paper [Efficient Range Minimum Queries using
/// Binary Indexed Trees](https://ioinformatics.org/journal/v9_2015_39_44.pdf), but since we are
/// only interested in `i..` queries (and not the more general `a..b`) we can get away with storing
/// only a single BIT (BIT2 in the paper).
pub struct BitHistory<S> {
    tree: Vec<S>,
}

impl<S> Default for BitHistory<S> {
    fn default() -> Self {
        Self::new()
    }
}

impl<S> FromIterator<S::Element> for BitHistory<S>
where
    S: Set,
{
    fn from_iter<T: IntoIterator<Item = S::Element>>(iter: T) -> Self {
        Self::from_iter(iter)
    }
}

impl<S> BitHistory<S> {
    pub const fn new() -> Self {
        Self { tree: Vec::new() }
    }

    pub fn len(&self) -> usize {
        self.tree.len()
    }

    /// Create a tree from a list of items.
    ///
    /// Time Complexity: `O(n)`
    pub fn from_iter(elements: impl IntoIterator<Item = S::Element>) -> Self
    where
        S: Set,
    {
        let mut tree = Vec::from_iter(elements.into_iter().map(S::make));
        let len = tree.len();

        for i in (1..len + 1).rev() {
            let parent = i - lsb(i);
            if parent > 0 {
                let (parents, children) = tree.split_at_mut(i - 1);
                parents[parent - 1].merge(&children[0]);
            }
        }

        Self { tree }
    }

    /// Push a new element to the end of the list.
    ///
    /// Time Complexity: `O(log n)`
    pub fn push(&mut self, element: S::Element) -> usize
    where
        S: Set,
    {
        let index = self.tree.len();

        let mut i = index + 1;
        loop {
            i -= lsb(i);
            if i == 0 {
                break;
            }
            self.tree[i - 1].insert(&element);
        }

        self.tree.push(S::make(element));

        index
    }

    /// Calls the `reduce` function with `O(log n)` subsets whose union is the values in the given
    /// `range`.
    pub fn query<'a>(&'a self, range: std::ops::RangeFrom<usize>, mut reduce: impl FnMut(&'a S)) {
        let mut i = range.start + 1;
        while i <= self.tree.len() {
            reduce(&self.tree[i - 1]);
            i += lsb(i);
        }
    }
}

/// Returns the least significant bit of `x`
fn lsb(x: usize) -> usize {
    x & (!x).wrapping_add(1)
}

/// A type representing an abstract set of elements.
pub trait Set {
    /// The type of elements stored in the set.
    type Element;
    /// Create a new set containing a single element.
    fn make(element: Self::Element) -> Self;
    /// Insert a new element into the set.
    fn insert(&mut self, element: &Self::Element);
    /// Insert all the items from the other set.
    fn merge(&mut self, other: &Self);
}

impl<S> Set for Option<S>
where
    S: Set + Clone,
    S::Element: Clone,
{
    type Element = Option<S::Element>;

    fn make(element: Self::Element) -> Self {
        Some(S::make(element?))
    }

    fn insert(&mut self, element: &Self::Element) {
        if let Some(element) = element {
            match self {
                None => *self = Some(S::make(element.clone())),
                Some(inner) => inner.insert(element),
            }
        }
    }

    fn merge(&mut self, other: &Self) {
        if let Some(other) = other {
            match self {
                None => *self = Some(other.clone()),
                Some(inner) => inner.merge(other),
            }
        }
    }
}

pub mod sets {
    //! Multiple [`Set`] implementations

    use super::Set;

    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct MinSet<T> {
        pub min: T,
    }

    impl<T> Set for MinSet<T>
    where
        T: Ord + Clone,
    {
        type Element = T;

        fn make(element: Self::Element) -> Self {
            Self { min: element }
        }

        fn insert(&mut self, element: &Self::Element) {
            if element < &self.min {
                self.min = element.clone();
            }
        }

        fn merge(&mut self, other: &Self) {
            self.insert(&other.min);
        }
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct MaxSet<T> {
        pub max: T,
    }

    impl<T> Set for MaxSet<T>
    where
        T: Ord + Clone,
    {
        type Element = T;

        fn make(element: Self::Element) -> Self {
            Self { max: element }
        }

        fn insert(&mut self, element: &Self::Element) {
            if element < &self.max {
                self.max = element.clone();
            }
        }

        fn merge(&mut self, other: &Self) {
            self.insert(&other.max);
        }
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub struct RangeSet<T> {
        pub min: T,
        pub max: T,
    }

    impl<T> Set for RangeSet<T>
    where
        T: Ord + Clone,
    {
        type Element = T;

        fn make(element: Self::Element) -> Self {
            Self {
                min: element.clone(),
                max: element,
            }
        }

        fn insert(&mut self, element: &Self::Element) {
            if element < &self.min {
                self.min = element.clone();
            }
            if element > &self.max {
                self.max = element.clone();
            }
        }

        fn merge(&mut self, other: &Self) {
            if other.min < self.min {
                self.min = other.min.clone();
            }
            if other.max > self.max {
                self.min = other.max.clone();
            }
        }
    }

    impl<T> super::BitHistory<MinSet<T>>
    where
        T: Ord,
    {
        /// Get the minimum value in the range in `O(log n)` time.
        pub fn min_query(&self, range: std::ops::RangeFrom<usize>) -> Option<&T> {
            let mut min = None;

            self.query(range, |set| match min {
                Some(min) if min < &set.min => {}
                _ => min = Some(&set.min),
            });

            min
        }
    }

    impl<T> super::BitHistory<MaxSet<T>>
    where
        T: Ord,
    {
        /// Get the maximum value in the range in `O(log n)` time.
        pub fn max_query(&self, range: std::ops::RangeFrom<usize>) -> Option<&T> {
            let mut max = None;

            self.query(range, |set| match max {
                Some(max) if max > &set.max => {}
                _ => max = Some(&set.max),
            });

            max
        }
    }

    impl<T> super::BitHistory<RangeSet<T>>
    where
        T: Ord,
    {
        /// Get the range spanned by values in the given index range.
        ///
        /// Time Complexity: `O(log n)`.
        pub fn range(&self, range: std::ops::RangeFrom<usize>) -> Option<(&T, &T)> {
            let mut min = None;
            let mut max = None;

            self.query(range, |set| {
                match min {
                    Some(min) if min < &set.min => {}
                    _ => min = Some(&set.min),
                }
                match max {
                    Some(max) if max > &set.max => {}
                    _ => max = Some(&set.max),
                }
            });

            Some((min?, max?))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type MinHistory = BitHistory<sets::MinSet<u32>>;

    #[test]
    fn revision_history_query() {
        let mut history = MinHistory::new();
        history.push(1);
        history.push(2);
        history.push(3);
        assert_eq!(history.min_query(0..), Some(&1));
        assert_eq!(history.min_query(1..), Some(&2));
        assert_eq!(history.min_query(2..), Some(&3));
    }

    #[test]
    fn revision_history_from_vec() {
        let history = MinHistory::from_iter(vec![1, 2, 3, 1, 8, 5, 6, 9]);
        assert_eq!(history.min_query(0..), Some(&1));
        assert_eq!(history.min_query(1..), Some(&1));
        assert_eq!(history.min_query(2..), Some(&1));
        assert_eq!(history.min_query(3..), Some(&1));
        assert_eq!(history.min_query(4..), Some(&5));
        assert_eq!(history.min_query(5..), Some(&5));
        assert_eq!(history.min_query(6..), Some(&6));
        assert_eq!(history.min_query(7..), Some(&9));
    }

    #[test]
    fn revision_history_sequential() {
        let mut history = MinHistory::new();
        for i in 0..32 {
            history.push(i as u32);
            assert_eq!(history.min_query(i..), Some(&(i as u32)));
        }

        let mut history = MinHistory::new();
        for i in 0..32 {
            history.push(32 - i as u32);
            assert_eq!(history.min_query(i..), Some(&(32 - i as u32)));
        }
    }

    fn xorshift(state: &mut u32) -> u32 {
        let mut x = *state;
        x ^= x << 13;
        x ^= x >> 17;
        x ^= x << 5;
        *state = x;
        x
    }

    #[test]
    fn revision_history_random() {
        let mut rng = 123;
        for count in 1..=128 {
            let values = (0..count).map(|_| xorshift(&mut rng)).collect::<Vec<_>>();

            let mut minimums = values.clone();
            let mut min = u32::MAX;
            for i in (0..count).rev() {
                min = std::cmp::min(minimums[i], min);
                minimums[i] = min;
            }

            let history = MinHistory::from_iter(values);

            for _ in 0..10 {
                for (i, min) in minimums.iter().enumerate() {
                    assert_eq!(history.min_query(i..), Some(min));
                }
            }
        }
    }
}
