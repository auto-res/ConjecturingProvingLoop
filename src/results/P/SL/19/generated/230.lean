

theorem Topology.closure_diff_closure_subset_closure_diff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure A \ closure B ⊆ closure (A \ B) := by
  intro x hx
  rcases hx with ⟨hxA, hxNotB⟩
  -- We prove `x ∈ closure (A \ B)` via the characterization
  -- of the closure in terms of open neighbourhoods.
  have hMem : ∀ U, IsOpen U → x ∈ U → ((U ∩ (A \ B) : Set X)).Nonempty := by
    intro U hU hxU
    -- Choose an open neighbourhood of `x` disjoint from `B`.
    have hV : IsOpen ((closure B)ᶜ) :=
      (isClosed_closure (s := B)).isOpen_compl
    have hxV : x ∈ (closure B)ᶜ := by
      simpa using hxNotB
    -- Intersect the two open neighbourhoods.
    let W := U ∩ (closure B)ᶜ
    have hW_open : IsOpen W := hU.inter hV
    have hxW : x ∈ W := And.intro hxU hxV
    -- Since `x ∈ closure A`, `W ∩ A` is nonempty.
    have hNon : ((W ∩ A : Set X)).Nonempty :=
      (mem_closure_iff).1 hxA W hW_open hxW
    rcases hNon with ⟨y, ⟨⟨hyU, hyV⟩, hyA⟩⟩
    -- `y ∉ B` because `y ∈ (closure B)ᶜ`, hence `y ∈ A \ B`.
    have hyNotB : y ∉ B := by
      intro hyB
      have : (y : X) ∈ closure B := subset_closure hyB
      exact hyV this
    exact ⟨y, And.intro hyU (And.intro hyA hyNotB)⟩
  exact (mem_closure_iff).2 hMem