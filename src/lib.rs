use core::{mem};

type usize = u16;
type isize = i16;
type NonZeroUsize = core::num::NonZeroU16;

mod kani_proofs;

/// The layout of a type which might be dynamically-sized.
///
/// `DstLayout` describes the layout of sized types, slice types, and "slice
/// DSTs" - ie, those that are known by the type system to have a trailing slice
/// (as distinguished from `dyn Trait` types - such types *might* have a
/// trailing slice type, but the type system isn't aware of it).
///
/// # Safety
///
/// Unlike [`core::alloc::Layout`], `DstLayout` is only used to describe full
/// Rust types - ie, those that satisfy the layout requirements outlined by
/// [the reference]. Callers may assume that an instance of `DstLayout`
/// satisfies any conditions imposed on Rust types by the reference.
///
/// If `layout: DstLayout` describes a type, `T`, then it is guaranteed that:
/// - `layout.align` is equal to `T`'s alignment
/// - If `layout.size_info` is `SizeInfo::Sized { size }`, then `T: Sized` and
///   `size_of::<T>() == size`
/// - If `layout.size_info` is `SizeInfo::SliceDst(slice_layout)`, then
///   - `T` is a slice DST
/// - The `size` of an instance of `T` with `elems` trailing slice elements is
///   equal to `slice_layout.offset + slice_layout.elem_size * elems` rounded up
///   to the nearest multiple of `layout.align`. Any bytes in the range
///   `[slice_layout.offset + slice_layout.elem_size * elems, size)` are padding
///   and must not be assumed to be initialized.
///
/// [the reference]: https://doc.rust-lang.org/reference/type-layout.html
#[doc(hidden)]
#[allow(missing_debug_implementations, missing_copy_implementations)]
#[cfg_attr(any(test, kani), derive(Copy, Clone, Debug, PartialEq, Eq))]
pub struct DstLayout {
    _align: NonZeroUsize,
    _size_info: SizeInfo,
}

#[cfg_attr(any(test, kani), derive(Copy, Clone, Debug, PartialEq, Eq))]
enum SizeInfo<E = usize> {
    Sized { _size: usize },
    SliceDst(TrailingSliceLayout<E>),
}

#[cfg_attr(any(test, kani), derive(Copy, Clone, Debug, PartialEq, Eq))]
struct TrailingSliceLayout<E = usize> {
    // The offset of the first byte of the trailing slice field. Note that this
    // is NOT the same as the minimum size of the type. For example, consider
    // the following type:
    //
    //   struct Foo {
    //       a: u16,
    //       b: u8,
    //       c: [u8],
    //   }
    //
    // In `Foo`, `c` is at byte offset 3. When `c.len() == 0`, `c` is followed
    // by a padding byte.
    _offset: usize,
    // The size of the element type of the trailing slice field.
    _elem_size: E,
}

impl SizeInfo {
    /// Attempts to create a `SizeInfo` from `Self` in which `elem_size` is a
    /// `NonZeroUsize`. If `elem_size` is 0, returns `None`.
    const fn _try_to_nonzero_elem_size(&self) -> Option<SizeInfo<NonZeroUsize>> {
        Some(match *self {
            SizeInfo::Sized { _size } => SizeInfo::Sized { _size },
            SizeInfo::SliceDst(TrailingSliceLayout { _offset, _elem_size }) => {
                if let Some(_elem_size) = NonZeroUsize::new(_elem_size) {
                    SizeInfo::SliceDst(TrailingSliceLayout { _offset, _elem_size })
                } else {
                    return None;
                }
            }
        })
    }
}

#[cfg_attr(any(test, kani), derive(Copy, Clone, Debug))]
enum _CastType {
    _Prefix,
    _Suffix,
}

impl DstLayout {
    /// Constructs a `DstLayout` which describes `T`.
    ///
    /// # Safety
    ///
    /// Unsafe code may assume that `DstLayout` is the correct layout for `T`.
    const fn for_type<T>() -> DstLayout {
        // SAFETY: `align` is correct by construction. `T: Sized`, and so it is
        // sound to initialize `size_info` to `SizeInfo::Sized { size }`; the
        // `size` field is also correct by construction.
        DstLayout {
            _align: match NonZeroUsize::new(mem::align_of::<T>() as _) {
                Some(align) => align,
                None => unreachable!(),
            },
            _size_info: SizeInfo::Sized { _size: mem::size_of::<T>() as _ },
        }
    }

    /// Constructs a `DstLayout` which describes `[T]`.
    ///
    /// # Safety
    ///
    /// Unsafe code may assume that `DstLayout` is the correct layout for `[T]`.
    const fn for_slice<T>() -> DstLayout {
        // SAFETY: The alignment of a slice is equal to the alignment of its
        // element type, and so `align` is initialized correctly.
        //
        // Since this is just a slice type, there is no offset between the
        // beginning of the type and the beginning of the slice, so it is
        // correct to set `offset: 0`. The `elem_size` is correct by
        // construction. Since `[T]` is a (degenerate case of a) slice DST, it
        // is correct to initialize `size_info` to `SizeInfo::SliceDst`.
        DstLayout {
            _align: match NonZeroUsize::new(mem::align_of::<T>() as _ ) {
                Some(align) => align,
                None => unreachable!(),
            },
            _size_info: SizeInfo::SliceDst(TrailingSliceLayout {
                _offset: 0,
                _elem_size: mem::size_of::<T>() as _,
            }),
        }
    }

    /// Validates that a cast is sound from a layout perspective.
    ///
    /// Validates that the size and alignment requirements of a type with the
    /// layout described in `self` would not be violated by performing a
    /// `cast_type` cast from a pointer with address `addr` which refers to a
    /// memory region of size `bytes_len`.
    ///
    /// If the cast is valid, `validate_cast_and_convert_metadata` returns
    /// `(elems, split_at)`. If `self` describes a dynamically-sized type, then
    /// `elems` is the maximum number of trailing slice elements for which a
    /// cast would be valid (for sized types, `elem` is meaningless and should
    /// be ignored). `split_at` is the index at which to split the memory region
    /// in order for the prefix (suffix) to contain the result of the cast, and
    /// in order for the remaining suffix (prefix) to contain the leftover
    /// bytes.
    ///
    /// There are three conditions under which a cast can fail:
    /// - The smallest possible value for the type is larger than the provided
    ///   memory region
    /// - A prefix cast is requested, and `addr` does not satisfy `self`'s
    ///   alignment requirement
    /// - A suffix cast is requested, and `addr + bytes_len` does not satisfy
    ///   `self`'s alignment requirement (as a consequence, since all instances
    ///   of the type are a multiple of its alignment, no size for the type will
    ///   result in a starting address which is properly aligned)
    ///
    /// # Safety
    ///
    /// The caller may assume that this implementation is correct, and may rely
    /// on that assumption for the soundness of their code. In particular, the
    /// caller may assume that, if `validate_cast_and_convert_metadata` returns
    /// `Some((elems, split_at))`, then:
    /// - A pointer to the type (for dynamically sized types, this includes
    ///   `elems` as its pointer metadata) describes an object of size `size <=
    ///   bytes_len`
    /// - If this is a prefix cast:
    ///   - `addr` satisfies `self`'s alignment
    ///   - `size == split_at`
    /// - If this is a suffix cast:
    ///   - `split_at == bytes_len - size`
    ///   - `addr + split_at` satisfies `self`'s alignment
    ///
    /// Note that this method does *not* ensure that a pointer constructed from
    /// its return values will be a valid pointer. In particular, this method
    /// does not reason about `isize` overflow, which is a requirement of many
    /// Rust pointer APIs, and may at some point be determined to be a validity
    /// invariant of pointer types themselves. This should never be a problem so
    /// long as the arguments to this method are derived from a known-valid
    /// pointer (e.g., one derived from a safe Rust reference), but it is
    /// nonetheless the caller's responsibility to justify that pointer
    /// arithmetic will not overflow based on a safety argument *other than* the
    /// mere fact that this method returned successfully.
    ///
    /// # Panics
    ///
    /// If `addr + bytes_len` overflows `usize`,
    /// `validate_cast_and_convert_metadata` may panic, or it may return
    /// incorrect results. No guarantees are made about when
    /// `validate_cast_and_convert_metadata` will panic. The caller should not
    /// rely on `validate_cast_and_convert_metadata` panicking in any particular
    /// condition, even if `debug_assertions` are enabled.
    const fn _validate_cast_and_convert_metadata(
        &self,
        addr: usize,
        bytes_len: usize,
        cast_type: _CastType,
    ) -> Option<(usize, usize)> {
        // `debug_assert!`, but with `#[allow(clippy::arithmetic_side_effects)]`.
        macro_rules! __debug_assert {
            ($e:expr $(, $msg:expr)?) => {
                debug_assert!({
                    #[allow(clippy::arithmetic_side_effects)]
                    let e = $e;
                    e
                } $(, $msg)?);
            };
        }

        // Note that, in practice, `self` is always a compile-time constant. We
        // do this check earlier than needed to ensure that we always panic as a
        // result of bugs in the program (such as calling this function on an
        // invalid type) instead of allowing this panic to be hidden if the cast
        // would have failed anyway for runtime reasons (such as a too-small
        // memory region).
        //
        // TODO(#67): Once our MSRV is 1.65, use let-else:
        // https://blog.rust-lang.org/2022/11/03/Rust-1.65.0.html#let-else-statements
        let size_info = match self._size_info._try_to_nonzero_elem_size() {
            Some(size_info) => size_info,
            None => panic!("attempted to cast to slice type with zero-sized element"),
        };

        // Precondition
        __debug_assert!(addr.checked_add(bytes_len).is_some(), "`addr` + `bytes_len` > usize::MAX");

        // Alignment checks go in their own block to avoid introducing variables
        // into the top-level scope.
        {
            // We check alignment for `addr` (for prefix casts) or `addr +
            // bytes_len` (for suffix casts). For a prefix cast, the correctness
            // of this check is trivial - `addr` is the address the object will
            // live at.
            //
            // For a suffix cast, we know that all valid sizes for the type are
            // a multiple of the alignment (and by safety precondition, we know
            // `DstLayout` may only describe valid Rust types). Thus, a
            // validly-sized instance which lives at a validly-aligned address
            // must also end at a validly-aligned address. Thus, if the end
            // address for a suffix cast (`addr + bytes_len`) is not aligned,
            // then no valid start address will be aligned either.
            let offset = match cast_type {
                _CastType::_Prefix => 0,
                _CastType::_Suffix => bytes_len,
            };

            // Addition is guaranteed not to overflow because `offset <=
            // bytes_len`, and `addr + bytes_len <= usize::MAX` is a
            // precondition of this method. Modulus is guaranteed not to divide
            // by 0 because `align` is non-zero.
            #[allow(clippy::arithmetic_side_effects)]
            if (addr + offset) % self._align.get() != 0 {
                return None;
            }
        }

        let (elems, self_bytes) = match size_info {
            SizeInfo::Sized { _size: size } => {
                if size > bytes_len {
                    return None;
                }
                (0, size)
            }
            SizeInfo::SliceDst(TrailingSliceLayout { _offset: offset, _elem_size: elem_size }) => {
                // Calculate the maximum number of bytes that could be consumed
                // - any number of bytes larger than this will either not be a
                // multiple of the alignment, or will be larger than
                // `bytes_len`.
                let max_total_bytes =
                    _round_down_to_next_multiple_of_alignment(bytes_len, self._align);
                // Calculate the maximum number of bytes that could be consumed
                // by the trailing slice.
                //
                // TODO(#67): Once our MSRV is 1.65, use let-else:
                // https://blog.rust-lang.org/2022/11/03/Rust-1.65.0.html#let-else-statements
                let max_slice_and_padding_bytes = match max_total_bytes.checked_sub(offset) {
                    Some(max) => max,
                    // `bytes_len` too small even for 0 trailing slice elements.
                    None => return None,
                };

                // // Calculate the number of elements that fit in
                // // `max_slice_and_padding_bytes`; any remaining bytes will be
                // // considered padding.
                // //
                // // Guaranteed not to divide by zero: `elem_size` is non-zero.
                // #[allow(clippy::arithmetic_side_effects)]
                // let elems = max_slice_and_padding_bytes / elem_size.get();
                // // Guaranteed not to overflow on multiplication: `usize::MAX >=
                // // max_slice_and_padding_bytes >= (max_slice_and_padding_bytes /
                // // elem_size) * elem_size`.
                // //
                // // Guaranteed not to overflow on addition:
                // // - max_slice_and_padding_bytes == max_total_bytes - offset
                // // - elems * elem_size <= max_slice_and_padding_bytes == max_total_bytes - offset
                // // - elems * elem_size + offset <= max_total_bytes <= usize::MAX
                // #[allow(clippy::arithmetic_side_effects)]
                // let without_padding = offset + elems * elem_size.get();

                let padding = max_slice_and_padding_bytes % elem_size.get();
                let elems = max_slice_and_padding_bytes / elem_size.get();

                let without_padding = offset + (max_slice_and_padding_bytes - padding);

                // `self_bytes` is equal to the offset bytes plus the bytes
                // consumed by the trailing slice plus any padding bytes
                // required to satisfy the alignment. Note that we have computed
                // the maximum number of trailing slice elements that could fit
                // in `self_bytes`, so any padding is guaranteed to be less than
                // the size of an extra element.
                //
                // Guaranteed not to overflow:
                // - By previous comment: without_padding == elems * elem_size +
                //   offset <= max_total_bytes
                // - By construction, `max_total_bytes` is a multiple of
                //   `self._align`.
                // - At most, adding padding needed to round `without_padding`
                //   up to the next multiple of the alignment will bring
                //   `self_bytes` up to `max_total_bytes`.
                #[allow(clippy::arithmetic_side_effects)]
                let self_bytes = without_padding
                    + _padding_needed_for(without_padding, self._align);
                (elems, self_bytes)
            }
        };

        __debug_assert!(self_bytes <= bytes_len);

        let split_at = match cast_type {
            _CastType::_Prefix => self_bytes,
            // Guaranteed not to underflow:
            // - In the `Sized` branch, only returns `size` if `size <=
            //   bytes_len`.
            // - In the `SliceDst` branch, calculates `self_bytes <=
            //   max_toatl_bytes`, which is upper-bounded by `bytes_len`.
            #[allow(clippy::arithmetic_side_effects)]
            _CastType::_Suffix => bytes_len - self_bytes,
        };

        Some((elems, split_at))
    }
}

/// Round `n` down to the largest value `m` such that `m <= n` and `m % align ==
/// 0`.
///
/// # Panics
///
/// May panic if `align` is not a power of two. Even if it doesn't panic in this
/// case, it will produce nonsense results.
#[inline(always)]
pub(crate) const fn _round_down_to_next_multiple_of_alignment(
    n: usize,
    align: NonZeroUsize,
) -> usize {
    let align = align.get();
    debug_assert!(align.is_power_of_two());

    // Subtraction can't underflow because `align.get() >= 1`.
    #[allow(clippy::arithmetic_side_effects)]
    let mask = !(align - 1);
    n & mask
}

/// Returns the amount of padding we must insert after `len` bytes to ensure
/// that the following address will satisfy `align` (measured in bytes).
///
/// e.g., if `len` is 9, then `padding_needed_for(len, 4)` returns 3, because
/// that is the minimum number of bytes of padding required to get a 4-aligned
/// address (assuming that the corresponding memory block starts at a 4-aligned
/// address).
///
/// The return value of this function has no meaning if `align` is not a
/// power-of-two.
///
/// # Panics
///
/// May panic if `align` is not a power of two.
#[inline(always)]
pub(crate) const fn _padding_needed_for(len: usize, align: NonZeroUsize) -> usize {
    // Rounded up value is:
    //   len_rounded_up = (len + align - 1) & !(align - 1);
    // and then we return the padding difference: `len_rounded_up - len`.
    //
    // We use modular arithmetic throughout:
    //
    // 1. align is guaranteed to be > 0, so align - 1 is always
    //    valid.
    //
    // 2. `len + align - 1` can overflow by at most `align - 1`,
    //    so the &-mask with `!(align - 1)` will ensure that in the
    //    case of overflow, `len_rounded_up` will itself be 0.
    //    Thus the returned padding, when added to `len`, yields 0,
    //    which trivially satisfies the alignment `align`.
    //
    // (Of course, attempts to allocate blocks of memory whose
    // size and padding overflow in the above manner should cause
    // the allocator to yield an error anyway.)

    let align = align.get();
    debug_assert!(align.is_power_of_two());
    let len_rounded_up = len.wrapping_add(align).wrapping_sub(1) & !align.wrapping_sub(1);
    len_rounded_up.wrapping_sub(len)
}
