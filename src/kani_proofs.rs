#![cfg(kani)]

use crate::*;


impl kani::Arbitrary for DstLayout {
    // TODO: Safety comments inline that justify that we could generate any
    // possible valid `DstLayout`.
    fn any() -> Self {
        let align: NonZeroUsize = kani::any();
        kani::assume(align.is_power_of_two());
       // kani::assume(align.get() <= (1 << 14));

        let offset: usize = kani::any();
        kani::assume(offset <= isize::MAX as usize);

        let size_info = if kani::any() {
            kani::assume(offset % align == 0);
            SizeInfo::Sized { _size: offset }
        } else {
            let min_size = offset + _padding_needed_for(offset, align);
            kani::assume(min_size <= isize::MAX as usize);
            let elem_size: NonZeroUsize = kani::any();
            SizeInfo::SliceDst(TrailingSliceLayout {
                _offset: offset,
                _elem_size: elem_size.get(),
            })
        };

        DstLayout { _align: align, _size_info: size_info }
    }
}

impl kani::Arbitrary for _CastType {
    fn any() -> Self {
        if kani::any() {
            _CastType::_Prefix
        } else {
            _CastType::_Suffix
        }
    }
}

/// Generate arguments to `validate_cast_and_convert_metadata` that satisfy its
/// documented preconditions.
fn validate_cast_and_convert_metadata_arguments() -> (usize, usize, _CastType) {
    let addr: usize = kani::any();
    let bytes_len: usize = kani::any();

    // bytes_len must be within the maximum valid allocation size in Rust
    kani::assume(bytes_len < isize::MAX as usize);

    // addr + bytes_len must not overflow usize
    kani::assume(addr.checked_add(bytes_len).is_some());

    (addr, bytes_len, kani::any())
}

// Validates that `validate_cast_and_convert_metadata` satisfies its own
// documented safety postconditions, and also a few other properties
// that aren't documented but we want to guarantee anyway.
fn validate_behavior<const ASSERTION_NUMBER: usize>(
    (layout, addr, bytes_len, cast_type): (DstLayout, usize, usize, _CastType),
) {
    if let Some((elems, split_at)) =
        layout._validate_cast_and_convert_metadata(addr, bytes_len, cast_type)
    {
        let (size_info, align) = (layout._size_info, layout._align);
        // If this is a sized type (no trailing slice), then `elems` is
        // meaningless, but in practice we set it to 0. Callers are not
        // allowed to rely on this, but a lot of math is nicer if
        // they're able to, and some callers might accidentally do that.
        let sized = matches!(layout._size_info, SizeInfo::Sized { .. });

        if ASSERTION_NUMBER == 0 {
            assert!(!(sized && elems != 0), "{}", "");
        }

        let resulting_size = match layout._size_info {
            SizeInfo::Sized { _size } => _size,
            SizeInfo::SliceDst(TrailingSliceLayout {
                _offset: offset,
                _elem_size: elem_size,
            }) => {
                // TODO: Explain why this logic is correct for both prefix and suffix casts.
                let max_total_bytes = bytes_len - (bytes_len % align);
                let max_total_slice_and_padding_bytes = max_total_bytes - offset;
                let slice_bytes = max_total_slice_and_padding_bytes - (max_total_slice_and_padding_bytes % elem_size);
                let without_padding = offset + slice_bytes;
                let resulting_size = without_padding + _padding_needed_for(without_padding, align);

                if ASSERTION_NUMBER == 2 {
                    // Test that `validate_cast_and_convert_metadata` computed
                    // the largest possible value that fits in the given range.
                    // Do this by adding an extra `elem_size` to
                    // `without_padding` and then adding necesary padding. This
                    // quantity should either overflow `usize` (note the use of
                    // `checked_add`) or should produce a value which wouldn't
                    // fit in `bytes_len`.
                    if let Some(one_extra_padded) =
                        without_padding.checked_add(elem_size).and_then(|unpadded| {
                            unpadded.checked_add(_padding_needed_for(
                                unpadded,
                                align,
                            ))
                        })
                    {
                        assert!(one_extra_padded > bytes_len, "{}", "");
                    }
                }

                resulting_size
            }
        };
        if ASSERTION_NUMBER == 3 {
            // Test safety postconditions guaranteed by
            // `validate_cast_and_convert_metadata`.
            assert!(resulting_size <= bytes_len, "{}", "");
        }
        match cast_type {
            _CastType::_Prefix => {
                if ASSERTION_NUMBER == 4 {
                    assert_eq!(addr % align, 0, "{}", "");
                }
                if ASSERTION_NUMBER == 5 {
                    assert_eq!(resulting_size, split_at, "{}", "");
                }
            }
            _CastType::_Suffix => {
                if ASSERTION_NUMBER == 6 {
                    assert_eq!(split_at, bytes_len - resulting_size, "{}", "");
                }
                if ASSERTION_NUMBER == 7 {
                    assert_eq!((addr + split_at) % align, 0, "{}", "");
                }
            }
        }
    } else {
        let min_size = match layout._size_info {
            SizeInfo::Sized { _size } => _size,
            SizeInfo::SliceDst(TrailingSliceLayout { _offset, .. }) => {
                _offset + _padding_needed_for(_offset, layout._align)
            }
        };

        // If a cast is invalid, it is either because...
        // 1. there are insufficent bytes at the given region for type:
        let insufficient_bytes = bytes_len < min_size;
        // 2. performing the cast would misalign type:
        let base = match cast_type {
            _CastType::_Prefix => 0,
            _CastType::_Suffix => bytes_len,
        };
        let misaligned = (base + addr) % layout._align != 0;

        if ASSERTION_NUMBER == 8 {
            assert!(insufficient_bytes || misaligned);
        }
    }
}

/// Prove that `validate_cast_and_convert_metadata` does not panic for
/// inputs satisfying its preconditions.
/// 
/// To improve solver performance, this proof is split into four sub-proofs,
/// covering the domain of `validate_cast_and_convert_metadata`.
mod prove_validate_cast_and_convert_metadata {
    use super::*;

    #[kani::proof]
    fn prove_0() {
        let layout: DstLayout = kani::any();
        let (addr, bytes_len, cast_type) = validate_cast_and_convert_metadata_arguments();
        validate_behavior::<0>((layout, addr, bytes_len, cast_type));
    }

    #[kani::proof]
    fn prove_1() {
        let layout: DstLayout = kani::any();
        let (addr, bytes_len, cast_type) = validate_cast_and_convert_metadata_arguments();
        validate_behavior::<1>((layout, addr, bytes_len, cast_type));
    }


    #[kani::proof]
    fn prove_2() {
        let layout: DstLayout = kani::any();
        let (addr, bytes_len, cast_type) = validate_cast_and_convert_metadata_arguments();
        validate_behavior::<2>((layout, addr, bytes_len, cast_type));
    }


    #[kani::proof]
    fn prove_3() {
        let layout: DstLayout = kani::any();
        let (addr, bytes_len, cast_type) = validate_cast_and_convert_metadata_arguments();
        validate_behavior::<3>((layout, addr, bytes_len, cast_type));
    }


    #[kani::proof]
    fn prove_4() {
        let layout: DstLayout = kani::any();
        let (addr, bytes_len, cast_type) = validate_cast_and_convert_metadata_arguments();
        validate_behavior::<4>((layout, addr, bytes_len, cast_type));
    }


    #[kani::proof]
    fn prove_5_prefix_sized() {
        let layout: DstLayout = kani::any();
        let (addr, bytes_len, cast_type) = validate_cast_and_convert_metadata_arguments();
        kani::assume(matches!(layout._size_info, SizeInfo::Sized { .. }));
        kani::assume(matches!(cast_type, _CastType::_Prefix));
        validate_behavior::<5>((layout, addr, bytes_len, cast_type));
    }

    #[kani::proof]
    fn prove_5_suffix_sized() {
        let layout: DstLayout = kani::any();
        let (addr, bytes_len, cast_type) = validate_cast_and_convert_metadata_arguments();
        kani::assume(matches!(layout._size_info, SizeInfo::Sized { .. }));
        kani::assume(matches!(cast_type, _CastType::_Suffix));
        validate_behavior::<5>((layout, addr, bytes_len, cast_type));
    }

    #[kani::proof]
    fn prove_5_prefix_slicedst() {
        let layout: DstLayout = kani::any();
        let (addr, bytes_len, cast_type) = validate_cast_and_convert_metadata_arguments();
        kani::assume(matches!(layout._size_info, SizeInfo::SliceDst { .. }));
        kani::assume(matches!(cast_type, _CastType::_Prefix));
        validate_behavior::<5>((layout, addr, bytes_len, cast_type));
    }

    #[kani::proof]
    fn prove_5_suffix_slicedst() {
        let layout: DstLayout = kani::any();
        let (addr, bytes_len, cast_type) = validate_cast_and_convert_metadata_arguments();
        kani::assume(matches!(layout._size_info, SizeInfo::SliceDst { .. }));
        kani::assume(matches!(cast_type, _CastType::_Suffix));
        validate_behavior::<5>((layout, addr, bytes_len, cast_type));
    }

    #[kani::proof]
    fn prove_6() {
        let layout: DstLayout = kani::any();
        let (addr, bytes_len, cast_type) = validate_cast_and_convert_metadata_arguments();
        validate_behavior::<7>((layout, addr, bytes_len, cast_type));
    }


    #[kani::proof]
    fn prove_7() {
        let layout: DstLayout = kani::any();
        let (addr, bytes_len, cast_type) = validate_cast_and_convert_metadata_arguments();
        validate_behavior::<7>((layout, addr, bytes_len, cast_type));
    }

    #[kani::proof]
    fn prove_8() {
        let layout: DstLayout = kani::any();
        let (addr, bytes_len, cast_type) = validate_cast_and_convert_metadata_arguments();
        validate_behavior::<8>((layout, addr, bytes_len, cast_type));
    }
}
