

theorem P3_intersection_closed {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) : Topology.P3 A → Topology.P3 B → Topology.P3 (A ∩ B) := by
  intro hP3A hP3B
  -- First, translate `P3` into `P2` using the closedness of the sets.
  have hP2A : P2 A := (P3_iff_P2_for_closed (A := A) hA).1 hP3A
  have hP2B : P2 B := (P3_iff_P2_for_closed (A := B) hB).1 hP3B
  -- From closedness and `P2` we obtain `A = interior A` and `B = interior B`.
  have hEqA : (A : Set X) = interior A := P2_closed (A := A) hA hP2A
  have hEqB : (B : Set X) = interior B := P2_closed (A := B) hB hP2B
  -- Hence both `A` and `B` are open.
  have hA_open : IsOpen A := by
    simpa [hEqA.symm] using (isOpen_interior : IsOpen (interior A))
  have hB_open : IsOpen B := by
    simpa [hEqB.symm] using (isOpen_interior : IsOpen (interior B))
  -- The intersection of two open sets is open.
  have hAB_open : IsOpen (A ∩ B) := hA_open.inter hB_open
  -- Any open set satisfies `P3`.
  exact P3_of_open (A := A ∩ B) hAB_open

theorem P3_of_open_superset {X : Type*} [TopologicalSpace X] {A U : Set X} (hU : IsOpen U) (hAU : A ⊆ U) (hUcl : U ⊆ closure A) : Topology.P3 A := by
  intro x hxA
  have hxU : x ∈ U := hAU hxA
  have hUsub : (U : Set X) ⊆ interior (closure A) :=
    interior_maximal hUcl hU
  exact hUsub hxU

theorem exists_compact_P1_subset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ K, IsCompact K ∧ K ⊆ A ∧ Topology.P1 K := by
  refine ⟨(∅ : Set X), isCompact_empty, Set.empty_subset _, P1_empty (X := X)⟩

theorem P2_interior_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} (h : interior (closure A) = A) : Topology.P2 A := by
  -- First, observe that `A` is open because it is given as the interior of a set.
  have hA_open : IsOpen (A : Set X) := by
    have : IsOpen (interior (closure A)) := isOpen_interior
    simpa [h] using this
  -- Every open set satisfies `P2`.
  exact P2_of_open (A := A) hA_open