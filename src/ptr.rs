use std::{
    borrow::Borrow,
    fmt::{self, Debug},
    hash::{Hash, Hasher},
    ops::Deref,
};

/// Non-reference-counted read-only pointer.
pub struct Ptr<T>(*const T);

// Safety: Ptr only exposes read-only access to the value safely
unsafe impl<T: Send> Send for Ptr<T> {}
unsafe impl<T: Sync> Sync for Ptr<T> {}

impl<T> Ptr<T> {
    pub fn new(value: T) -> Self {
        Self(Box::into_raw(Box::new(value)))
    }

    /// # Safety
    ///
    /// This must be the only ptr to the value and not used after this call.
    pub unsafe fn into_owned(this: Self) -> Box<T> {
        Box::from_raw(this.0 as *mut T)
    }

    /// # Safety
    ///
    /// This must be the only ptr to the value and not used after this call.
    pub unsafe fn drop(this: Self) {
        drop(Self::into_owned(this));
    }
}

impl<T> Deref for Ptr<T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*self.0 }
    }
}

impl<T> Borrow<T> for Ptr<T> {
    fn borrow(&self) -> &T {
        self
    }
}

impl<T> Debug for Ptr<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(&**self, f)
    }
}

impl<T> Clone for Ptr<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Ptr<T> {}

impl<T> PartialEq for Ptr<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        **self == **other
    }
}

impl<T> Eq for Ptr<T> where T: Eq {}

impl<T> Hash for Ptr<T>
where
    T: Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state)
    }
}
