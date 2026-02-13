

theorem closure_diff_closure_subset_closure_diff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) \ closure B ⊆ closure (A \ B : Set X) := by
  intro x hx
  rcases hx with ⟨hxClA, hxNotClB⟩
  -- We will verify the neighbourhood criterion for `closure (A \ B)`.
  have h :
      ∀ U : Set X, IsOpen U → x ∈ U →
        ((U ∩ (A \ B)) : Set X).Nonempty := by
    intro U hU hxU
    -- Shrink the neighbourhood so that it is disjoint from `B`.
    have hOpenCompl : IsOpen ((closure B)ᶜ : Set X) :=
      isClosed_closure.isOpen_compl
    have hVopen : IsOpen (U ∩ (closure B)ᶜ) := hU.inter hOpenCompl
    have hxV : x ∈ U ∩ (closure B)ᶜ := by
      exact And.intro hxU hxNotClB
    -- Since `x ∈ closure A`, this neighbourhood meets `A`.
    have hNonempty :
        ((U ∩ (closure B)ᶜ) ∩ A : Set X).Nonempty :=
      (mem_closure_iff).1 hxClA (U ∩ (closure B)ᶜ) hVopen hxV
    rcases hNonempty with ⟨y, ⟨⟨hyU, hyNotClB⟩, hyA⟩⟩
    -- Points outside `closure B` are certainly outside `B`.
    have hyNotB : (y : X) ∉ B := by
      intro hyB
      have : (y : X) ∈ closure B := subset_closure hyB
      exact hyNotClB this
    -- Hence `y ∈ U ∩ (A \ B)`.
    exact ⟨y, ⟨hyU, ⟨hyA, hyNotB⟩⟩⟩
  -- Conclude that `x ∈ closure (A \ B)` by the neighbourhood criterion.
  exact (mem_closure_iff).2 h