

theorem dense_iff_open_inter_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) ↔
      ∀ U : Set X, IsOpen U → U.Nonempty → (A ∩ U : Set X).Nonempty := by
  classical
  constructor
  · intro hDense U hU_open hU_nonempty
    -- Use the forward implication supplied by `dense_inter_open_nonempty`.
    simpa using
      (dense_inter_open_nonempty (A := A) (U := U)
        hDense hU_open hU_nonempty)
  · intro hProp x
    -- Establish `x ∈ closure A` via the neighbourhood criterion.
    have hx_closure :
        (∀ V : Set X, IsOpen V → x ∈ V → (V ∩ A : Set X).Nonempty) := by
      intro V hV_open hxV
      -- `V` is nonempty because it contains `x`.
      have hV_nonempty : (V : Set X).Nonempty := ⟨x, hxV⟩
      -- Apply the assumed property to obtain a point of `A` in `V`.
      have hInter : (A ∩ V : Set X).Nonempty :=
        hProp V hV_open hV_nonempty
      -- Reorder the intersection to match the required form.
      simpa [Set.inter_comm] using hInter
    exact (mem_closure_iff).2 hx_closure