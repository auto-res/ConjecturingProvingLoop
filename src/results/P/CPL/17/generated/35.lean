

theorem P1_subsingleton_iff {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P1 A ↔ True := by
  constructor
  · intro _; trivial
  · intro _; simpa using (P1_subsingleton (X := X) (A := A))

theorem P2_subsingleton_iff {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P2 A ↔ True := by
  constructor
  · intro _; trivial
  · intro _; simpa using (P2_subsingleton (X := X) (A := A))

theorem P3_subsingleton_iff {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P3 A ↔ True := by
  constructor
  · intro _; trivial
  · intro _; simpa using (P3_subsingleton (X := X) (A := A))