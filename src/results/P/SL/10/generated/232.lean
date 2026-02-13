

theorem Topology.closure_diff_closure_subset_closure_diff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure A \ closure B ⊆ closure (A \ B) := by
  intro x hx
  rcases hx with ⟨hxClA, hxNotClB⟩
  -- We show that `x ∈ closure (A \ B)` using the neighbourhood criterion.
  have : x ∈ closure (A \ B) := by
    apply (mem_closure_iff).2
    intro U hUopen hxU
    -- Intersect the neighbourhood with the open complement of `closure B`.
    have hOpenCompl : IsOpen ((closure (B : Set X))ᶜ) :=
      (isClosed_closure : IsClosed (closure B)).isOpen_compl
    have hVopen : IsOpen (U ∩ (closure (B : Set X))ᶜ) :=
      hUopen.inter hOpenCompl
    have hxV : x ∈ U ∩ (closure (B : Set X))ᶜ :=
      ⟨hxU, hxNotClB⟩
    -- Since `x ∈ closure A`, this open set meets `A`.
    have hNonempty :
        (U ∩ (closure (B : Set X))ᶜ ∩ A).Nonempty :=
      (mem_closure_iff).1 hxClA _ hVopen hxV
    rcases hNonempty with ⟨y, ⟨hyU, hyNotClB⟩, hyA⟩
    -- The point `y` avoids `B`, hence lies in `A \ B`.
    have hyNotB : y ∉ B := by
      intro hyB
      have : y ∈ (closure (B : Set X)) := subset_closure hyB
      exact hyNotClB this
    exact ⟨y, ⟨hyU, ⟨hyA, hyNotB⟩⟩⟩
  exact this