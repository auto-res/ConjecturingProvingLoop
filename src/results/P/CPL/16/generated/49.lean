

theorem P1_prod_of_P2 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 A → P2 B → P1 (Set.prod A B) := by
  intro hA hB
  have hA' : P1 A := (P2_subset_P1 (A := A)) hA
  have hB' : P1 B := (P2_subset_P1 (A := B)) hB
  exact P1_prod hA' hB'

theorem P2_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → closure (interior (closure A)) = closure A := by
  intro hP2
  -- From `P2 A` we get `P1 A`.
  have hP1 : P1 A := (P2_subset_P1 (A := A)) hP2
  -- Hence, `P1 (closure A)`.
  have hP1Cl : P1 (closure A) := P1_closure (A := A) hP1
  -- Use the characterization `P1 S ↔ closure (interior S) = closure S`
  have hEq : closure (interior (closure A)) = closure (closure A) :=
    (P1_iff_closure_eq (A := closure A)).1 hP1Cl
  simpa [closure_closure] using hEq