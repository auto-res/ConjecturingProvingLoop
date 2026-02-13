

theorem interior_diff_closure_interior_eq_empty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior ((A : Set X) \ closure (interior A)) = (∅ : Set X) := by
  classical
  apply le_antisymm
  · intro x hx
    rcases mem_interior.1 hx with ⟨U, hUsub, hUopen, hxU⟩
    -- `U ⊆ A`
    have hUsubA : (U : Set X) ⊆ A := fun y hy => (hUsub hy).1
    -- Hence `U ⊆ interior A`
    have hUsubInt : (U : Set X) ⊆ interior (A : Set X) :=
      interior_maximal hUsubA hUopen
    -- So `x ∈ interior A ⊆ closure (interior A)`
    have hxInClInt : x ∈ closure (interior (A : Set X)) :=
      subset_closure (hUsubInt hxU)
    -- But `x ∉ closure (interior A)` since `U ⊆ (closure (interior A))ᶜ`
    have hxNotClInt : x ∉ closure (interior (A : Set X)) :=
      (hUsub hxU).2
    exact (hxNotClInt hxInClInt).elim
  · exact Set.empty_subset _