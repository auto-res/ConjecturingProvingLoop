

theorem Topology.interior_diff_closure_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A : Set X) \ closure (B : Set X) ⊆ interior (A \ B) := by
  rintro x ⟨hx_intA, hx_notClB⟩
  -- `interior A` is open.
  have h_open_intA : IsOpen (interior (A : Set X)) := isOpen_interior
  -- The complement of `closure B` is open as well.
  have h_open_compl : IsOpen ((closure (B : Set X))ᶜ) :=
    (isClosed_closure : IsClosed (closure (B : Set X))).isOpen_compl
  ------------------------------------------------------------------
  --  Construct an open neighbourhood of `x` contained in `A \ B`.
  ------------------------------------------------------------------
  let U := interior (A : Set X) ∩ (closure (B : Set X))ᶜ
  have hU_open : IsOpen U := h_open_intA.inter h_open_compl
  have hxU : (x : X) ∈ U := ⟨hx_intA, by
    -- `x ∉ closure B` gives membership in the complement.
    simpa using hx_notClB⟩
  -- Show that `U ⊆ A \ B`.
  have hU_subset : (U : Set X) ⊆ A \ B := by
    intro y hy
    have hA : (y : X) ∈ A :=
      (interior_subset : interior (A : Set X) ⊆ A) hy.1
    have h_notB : (y : X) ∉ B := by
      intro hyB
      have : (y : X) ∈ closure (B : Set X) := subset_closure hyB
      exact hy.2 this
    exact ⟨hA, h_notB⟩
  ------------------------------------------------------------------
  --  Conclude that `x` is in `interior (A \ B)`.
  ------------------------------------------------------------------
  exact
    (interior_maximal hU_subset hU_open) hxU