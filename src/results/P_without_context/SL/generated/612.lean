

theorem P2_implies_P3 {A : Set X} (hA : P2 A) : P3 A := by
  -- We start from the assumption that A ⊆ interior (closure (interior A))
  -- and aim to show A ⊆ interior (closure A).
  have hmono : interior (closure (interior A)) ⊆ interior (closure A) := by
    -- interior is monotone, so apply it to the inclusion
    -- closure (interior A) ⊆ closure A,
    -- which follows from the monotonicity of closure and interior_subset.
    have hcl : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    exact interior_mono hcl
  -- Compose the two inclusions.
  exact Set.Subset.trans hA hmono