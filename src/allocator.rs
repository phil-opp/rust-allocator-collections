pub unsafe trait Allocator {

    /// Return a pointer to `size` bytes of memory aligned to `align`.
    ///
    /// On failure, return a null pointer.
    ///
    /// Behavior is undefined if the requested size is 0 or the alignment is not a
    /// power of 2. The alignment must be no larger than the largest supported page
    /// size on the platform.
    unsafe fn allocate(&mut self, size: usize, align: usize) -> *mut u8;

    /// Resize the allocation referenced by `ptr` to `size` bytes.
    ///
    /// On failure, return a null pointer and leave the original allocation intact.
    ///
    /// If the allocation was relocated, the memory at the passed-in pointer is
    /// undefined after the call.
    ///
    /// Behavior is undefined if the requested size is 0 or the alignment is not a
    /// power of 2. The alignment must be no larger than the largest supported page
    /// size on the platform.
    ///
    /// The `old_size` and `align` parameters are the parameters that were used to
    /// create the allocation referenced by `ptr`. The `old_size` parameter may be
    /// any value in range_inclusive(requested_size, usable_size).
    unsafe fn reallocate(&mut self,
                         ptr: *mut u8,
                         old_size: usize,
                         size: usize,
                         align: usize)
                         -> *mut u8;

    /// Resize the allocation referenced by `ptr` to `size` bytes.
    ///
    /// If the operation succeeds, it returns `usable_size(size, align)` and if it
    /// fails (or is a no-op) it returns `usable_size(old_size, align)`.
    ///
    /// Behavior is undefined if the requested size is 0 or the alignment is not a
    /// power of 2. The alignment must be no larger than the largest supported page
    /// size on the platform.
    ///
    /// The `old_size` and `align` parameters are the parameters that were used to
    /// create the allocation referenced by `ptr`. The `old_size` parameter may be
    /// any value in range_inclusive(requested_size, usable_size).
    unsafe fn reallocate_inplace(&mut self,
                                 ptr: *mut u8,
                                 old_size: usize,
                                 size: usize,
                                 align: usize)
                                 -> usize;

    /// Deallocates the memory referenced by `ptr`.
    ///
    /// The `ptr` parameter must not be null.
    ///
    /// The `old_size` and `align` parameters are the parameters that were used to
    /// create the allocation referenced by `ptr`. The `old_size` parameter may be
    /// any value in range_inclusive(requested_size, usable_size).
    unsafe fn deallocate(&mut self, ptr: *mut u8, old_size: usize, align: usize);

    /// Returns the usable size of an allocation created with the specified the
    /// `size` and `align`.
    fn usable_size(&self, size: usize, align: usize) -> usize;
}
