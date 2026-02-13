

theorem interior_diff_subset_interior_diff {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB_closed : IsClosed B) :
    interior A \ closure B ⊆ interior (A \ B) := by
  intro x hx
  rcases hx with ⟨hxIntA, hxNotClB⟩
  -- Choose an open neighbourhood `U` of `x` contained in `A`.
  rcases (Set.mem_interior).1 hxIntA with ⟨U, hU_open, hU_subA, hxU⟩
  -- The complement of the closed set `B` is open.
  have hOpenCompl : IsOpen (Bᶜ) := by
    simpa using (isOpen_compl_iff).2 hB_closed
  -- `x` is not in `B`.
  have hxNotB : x ∉ B := by
    intro hxB
    have : (x : X) ∈ closure B := subset_closure hxB
    exact hxNotClB this
  -- Define the open set `V = U ∩ Bᶜ`.
  let V : Set X := U ∩ Bᶜ
  have hV_open : IsOpen V := hU_open.inter hOpenCompl
  have hV_sub : V ⊆ A \ B := by
    intro y hyV
    have hyA : y ∈ A := hU_subA hyV.1
    have hyNotB : y ∉ B := hyV.2
    exact And.intro hyA hyNotB
  have hxV : x ∈ V := And.intro hxU hxNotB
  -- Conclude that `x ∈ interior (A \ B)`.
  exact
    (Set.mem_interior).2 ⟨V, hV_open, hV_sub, hxV⟩