

theorem closure_subset_closure_interior_of_subset_and_P1
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP1B : Topology.P1 (X := X) B) (hAB : (A : Set X) ⊆ B) :
    closure (A : Set X) ⊆ closure (interior B) := by
  calc
    closure (A : Set X) ⊆ closure B := closure_mono hAB
    _ ⊆ closure (interior B) := by
      have h : (B : Set X) ⊆ closure (interior B) := hP1B
      have h' : closure (B : Set X) ⊆ closure (closure (interior B)) :=
        closure_mono h
      simpa [closure_closure] using h'