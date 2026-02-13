

theorem closure_diff_subset_closureDiff_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hB : IsClosed B) :
    closure A \ B ⊆ closure (A \ B) := by
  intro x hx
  rcases hx with ⟨hxClA, hxNotB⟩
  -- Use the neighborhood characterization of `closure`.
  have h :
      ∀ U : Set X, IsOpen U → x ∈ U → (U ∩ (A \ B)).Nonempty := by
    intro U hU_open hxU
    -- The complement of the closed set `B` is open.
    have hOpenCompl : IsOpen (Bᶜ) := by
      simpa using (isOpen_compl_iff).2 hB
    -- Intersect the neighborhood `U` with `Bᶜ`, which is still open.
    have hV_open : IsOpen (U ∩ Bᶜ) := hU_open.inter hOpenCompl
    have hxV : x ∈ U ∩ Bᶜ := And.intro hxU hxNotB
    -- Since `x ∈ closure A`, this open set meets `A`.
    have hNon : (U ∩ Bᶜ ∩ A).Nonempty :=
      (mem_closure_iff).1 hxClA (U ∩ Bᶜ) hV_open hxV
    -- Repackage the witness to lie in `U ∩ (A \ B)`.
    rcases hNon with ⟨y, hy⟩
    rcases hy with ⟨⟨hyU, hyNotB⟩, hyA⟩
    have hyNotB' : y ∉ B := by
      simpa using hyNotB
    exact ⟨y, And.intro hyU (And.intro hyA hyNotB')⟩
  -- Conclude that `x ∈ closure (A \ B)`.
  exact (mem_closure_iff).2 h