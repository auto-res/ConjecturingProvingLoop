

theorem interior_closure_nonempty_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hA : (A : Set X).Nonempty) :
    (interior (closure A)).Nonempty := by
  rcases hA with ⟨x, hxA⟩
  have hxCl : x ∈ closure (interior A) := hP1 hxA
  have hIntNonempty : (interior (A : Set X)).Nonempty := by
    by_contra hEmpty
    have hIntEq : interior (A : Set X) = (∅ : Set X) :=
      Set.not_nonempty_iff_eq_empty.mp hEmpty
    have : (x : X) ∈ (∅ : Set X) := by
      simpa [hIntEq, closure_empty] using hxCl
    exact this
  rcases hIntNonempty with ⟨y, hyIntA⟩
  have hSub : interior (A : Set X) ⊆ interior (closure A) :=
    Topology.interior_subset_interior_closure (A := A)
  have hyIntCl : y ∈ interior (closure A) := hSub hyIntA
  exact ⟨y, hyIntCl⟩