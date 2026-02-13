

theorem Topology.closure_diff_subset_closure_diff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure A \ closure B ⊆ closure (A \ B) := by
  intro x hx
  rcases hx with ⟨hxA, hxNotB⟩
  -- We prove the closure condition via neighbourhoods.
  have h :
      ∀ U, IsOpen U → x ∈ U → ((U ∩ (A \ B) : Set X)).Nonempty := by
    intro U hU hxU
    -- Intersect `U` with the open complement of `closure B`.
    let W : Set X := U ∩ (closure B)ᶜ
    have hW_open : IsOpen W :=
      hU.inter ((isClosed_closure (s := B)).isOpen_compl)
    have hxW : x ∈ W := by
      have hxComp : x ∈ (closure B)ᶜ := hxNotB
      exact And.intro hxU hxComp
    -- Since `x ∈ closure A`, `W ∩ A` is nonempty.
    have hNon : ((W ∩ A : Set X)).Nonempty :=
      (mem_closure_iff.1 hxA) W hW_open hxW
    rcases hNon with ⟨y, ⟨⟨hyU, hyComp⟩, hyA⟩⟩
    -- `y ∉ B` because `y ∈ (closure B)ᶜ ⊆ Bᶜ`.
    have hyNotB : y ∉ B := by
      intro hyB
      have : (y : X) ∈ closure B := subset_closure hyB
      exact hyComp this
    -- Thus, `y ∈ U ∩ (A \ B)`.
    exact ⟨y, ⟨hyU, And.intro hyA hyNotB⟩⟩
  exact (mem_closure_iff.2 h)