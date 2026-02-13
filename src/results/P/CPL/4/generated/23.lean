

theorem P2_countable_Union {X : Type*} [TopologicalSpace X] {s : ℕ → Set X} (h : ∀ n, Topology.P2 (s n)) : Topology.P2 (⋃ n, interior (s n)) := by
  have h' : ∀ n, Topology.P2 (interior (s n)) := by
    intro n
    exact P2_interior (X := X) (A := s n) (h n)
  simpa using
    (P2_Union_countable (X := X) (s := fun n => interior (s n)) h')

theorem P3_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : Topology.P3 A) (hB : Topology.P3 B) (hC : Topology.P3 C) (hD : Topology.P3 D) : Topology.P3 (Set.prod (Set.prod A B) (Set.prod C D)) := by
  -- First, obtain `P3` for the product `A × B`.
  have hAB : Topology.P3 (Set.prod A B) :=
    P3_prod (X := W) (Y := X) (A := A) (B := B) hA hB
  -- Next, obtain `P3` for the product `C × D`.
  have hCD : Topology.P3 (Set.prod C D) :=
    P3_prod (X := Y) (Y := Z) (A := C) (B := D) hC hD
  -- Finally, apply the product lemma once more to get the desired result.
  simpa using
    (P3_prod (X := W × X) (Y := Y × Z)
      (A := Set.prod A B) (B := Set.prod C D) hAB hCD)

theorem P3_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 (interior (closure A)) := by
  simpa using
    (openSet_P3 (X := X) (A := interior (closure A)) isOpen_interior)