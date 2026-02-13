

theorem Topology.P1_nonempty_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → A.Nonempty → (interior (closure A)).Nonempty := by
  intro hP1 hA
  -- Obtain a point in `interior A` from `P1` and the nonemptiness of `A`.
  have hIntA : (interior A).Nonempty :=
    Topology.P1_nonempty_interior (X := X) (A := A) hP1 hA
  rcases hIntA with ⟨x, hxIntA⟩
  -- Use monotonicity to see that this point also lies in `interior (closure A)`.
  have hxIntCl : x ∈ interior (closure A) :=
    (Topology.interior_subset_interior_closure (X := X) (A := A)) hxIntA
  exact ⟨x, hxIntCl⟩