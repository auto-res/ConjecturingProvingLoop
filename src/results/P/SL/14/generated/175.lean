

theorem Topology.dense_iff_interior_compl_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) ↔ interior (Aᶜ : Set X) = (∅ : Set X) := by
  classical
  -- Density is equivalent to `closure A = univ`.
  have h_dense :
      Dense (A : Set X) ↔ closure (A : Set X) = (Set.univ : Set X) :=
    dense_iff_closure_eq (s := (A : Set X))
  -- `interior (Aᶜ)` is the complement of `closure A`.
  have h_int_compl : interior (Aᶜ : Set X) = (closure (A : Set X))ᶜ := by
    simpa using interior_compl
  -- Relate `closure A = univ` to `interior (Aᶜ) = ∅`.
  have h_aux :
      closure (A : Set X) = (Set.univ : Set X) ↔
        interior (Aᶜ : Set X) = (∅ : Set X) := by
    constructor
    · intro h_cl
      have : interior (Aᶜ : Set X) = (Set.univ : Set X)ᶜ := by
        simpa [h_cl] using h_int_compl
      simpa [Set.compl_univ] using this
    · intro h_int
      -- From `h_int_compl`, the complement of the closure is empty.
      have h_compl : (closure (A : Set X))ᶜ = (∅ : Set X) := by
        have : interior (Aᶜ : Set X) = (closure (A : Set X))ᶜ := h_int_compl
        simpa [this] using h_int
      -- Therefore `closure A` is the whole space.
      have : closure (A : Set X) = ((closure (A : Set X))ᶜ)ᶜ := by
        simp
      simpa [h_compl, Set.compl_empty] using this
  simpa using h_dense.trans h_aux