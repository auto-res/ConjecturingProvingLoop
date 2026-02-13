

theorem interior_diff_eq_diff_closure_of_open
    {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen (U : Set X)) :
    interior (U \ V : Set X) = U \ closure V := by
  ext x
  constructor
  · intro hx
    -- From `x ∈ interior (U \ V)` we get `x ∈ U \ V`.
    have hxUV : x ∈ U \ V :=
      (interior_subset : interior (U \ V : Set X) ⊆ U \ V) hx
    have hxU : x ∈ U := hxUV.1
    -- Show that `x ∉ closure V`.
    have hxNotCl : x ∉ closure V := by
      by_contra hxCl
      -- `interior (U \ V)` is an open neighbourhood of `x`
      -- contained in `U \ V`, hence disjoint from `V`.
      have hOpenInt : IsOpen (interior (U \ V : Set X)) := isOpen_interior
      have hNonempty :
          ((interior (U \ V : Set X)) ∩ V : Set X).Nonempty :=
        (mem_closure_iff).1 hxCl (interior (U \ V : Set X)) hOpenInt hx
      rcases hNonempty with ⟨y, ⟨hyInt, hyV⟩⟩
      have : y ∈ U \ V :=
        (interior_subset : interior (U \ V : Set X) ⊆ U \ V) hyInt
      exact this.2 hyV
    exact ⟨hxU, hxNotCl⟩
  · rintro ⟨hxU, hxNotCl⟩
    -- Construct an open neighbourhood of `x` contained in `U \ V`.
    have hOpenCompl : IsOpen ((closure V)ᶜ : Set X) :=
      isClosed_closure.isOpen_compl
    have hOpenN : IsOpen (U ∩ (closure V)ᶜ : Set X) :=
      hU.inter hOpenCompl
    have hxN : x ∈ (U ∩ (closure V)ᶜ : Set X) := ⟨hxU, hxNotCl⟩
    have hSub :
        (U ∩ (closure V)ᶜ : Set X) ⊆ U \ V := by
      intro y hy
      rcases hy with ⟨hyU, hyNotCl⟩
      have hyNotV : y ∉ V := by
        intro hyV
        have : y ∈ closure V := subset_closure hyV
        exact hyNotCl this
      exact ⟨hyU, hyNotV⟩
    exact
      (interior_maximal hSub hOpenN) hxN