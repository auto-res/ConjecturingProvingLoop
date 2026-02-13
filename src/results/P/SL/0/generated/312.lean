

theorem P3_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 (closure (A : Set X)) →
    Topology.P3 (closure (B : Set X)) →
    Topology.P3 (closure (A ∪ B : Set X)) := by
  intro hA hB
  -- Each hypothesis gives the openness of the corresponding closure.
  have hOpenA : IsOpen (closure (A : Set X)) :=
    (Topology.isOpen_closure_of_P3_closure (X := X) (A := A)) hA
  have hOpenB : IsOpen (closure (B : Set X)) :=
    (Topology.isOpen_closure_of_P3_closure (X := X) (A := B)) hB
  -- Hence their union, which equals `closure (A ∪ B)`, is open.
  have hOpenUnion : IsOpen (closure (A ∪ B : Set X)) := by
    have h : IsOpen ((closure (A : Set X)) ∪ closure (B : Set X) : Set X) :=
      hOpenA.union hOpenB
    simpa [closure_union] using h
  -- An open set satisfies `P3`.
  exact
    (Topology.P3_closure_of_isOpen_closure (X := X) (A := A ∪ B)) hOpenUnion