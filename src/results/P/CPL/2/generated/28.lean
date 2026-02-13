

theorem P1_mul_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P1 (X:=X) A := by
  -- Unfold the definition of `P1`
  unfold Topology.P1
  intro x hxA
  -- In a subsingleton type, any non-empty set is the whole space
  have hAU : (A : Set X) = (Set.univ : Set X) := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      have : y = x := Subsingleton.elim y x
      simpa [this] using hxA
  -- Rewriting with this equality solves the goal
  have : x ∈ (Set.univ : Set X) := by simp
  simpa [hAU, interior_univ, closure_univ] using this

theorem P1_iff_P2_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h_open : IsOpen (closure A)) : (Topology.P1 (X:=X) A ↔ Topology.P2 (X:=X) A) := by
  -- `P3 A` holds automatically since the closure of `A` is open
  have hP3 : Topology.P3 (X := X) A :=
    P3_of_open_closure (X := X) (A := A) h_open
  constructor
  · intro hP1
    exact P2_of_P1_and_P3 (X := X) (A := A) hP1 hP3
  · intro hP2
    exact P1_of_P2 (A := A) hP2