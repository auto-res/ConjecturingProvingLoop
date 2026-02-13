

theorem closure_diff_closure_subset_closureDiff {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure A \ closure B ⊆ closure (A \ B) := by
  intro x hx
  rcases hx with ⟨hxA, hxNotB⟩
  -- To show that `x` is in `closure (A \ B)`, we use the neighborhood
  -- characterization of the closure.
  have h :
      ∀ U : Set X, IsOpen U → x ∈ U → (U ∩ (A \ B)).Nonempty := by
    intro U hU_open hxU
    -- Consider the open set `V = U ∩ (closure B)ᶜ`, which avoids `closure B`.
    have hOpenCompl : IsOpen ((closure B)ᶜ) := by
      have hClosed : IsClosed (closure B) := isClosed_closure
      simpa using (isOpen_compl_iff).2 hClosed
    have hV_open : IsOpen (U ∩ (closure B)ᶜ) := hU_open.inter hOpenCompl
    have hxV : x ∈ U ∩ (closure B)ᶜ := And.intro hxU hxNotB
    -- Because `x ∈ closure A`, the set `V` meets `A`.
    have hNon : ((U ∩ (closure B)ᶜ) ∩ A).Nonempty :=
      (mem_closure_iff).1 hxA (U ∩ (closure B)ᶜ) hV_open hxV
    -- Any such point of intersection lies in `U ∩ (A \ B)`.
    rcases hNon with ⟨y, ⟨hyU, hyNotClB⟩, hyA⟩
    -- Show that `y ∉ B`.
    have hyNotB : y ∉ B := by
      intro hyB
      have : (y : X) ∈ closure B := subset_closure hyB
      exact hyNotClB this
    exact ⟨y, And.intro hyU (And.intro hyA hyNotB)⟩
  -- Conclude that `x ∈ closure (A \ B)`.
  exact (mem_closure_iff).2 h