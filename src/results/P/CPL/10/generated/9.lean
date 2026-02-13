

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (Set.prod A B) := by
  intro x hx
  rcases x with ⟨a, b⟩
  rcases hx with ⟨ha, hb⟩
  have ha' : a ∈ closure (interior A) := hA ha
  have hb' : b ∈ closure (interior B) := hB hb
  have : (a, b) ∈ closure (interior (A ×ˢ B)) := by
    simpa [interior_prod_eq, closure_prod_eq] using And.intro ha' hb'
  exact this

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : closure (interior A) = Set.univ) : Topology.P2 A := by
  intro x hx
  simpa [hA, isOpen_univ.interior_eq] using (Set.mem_univ x)

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : closure (interior A) = Set.univ) : Topology.P3 A := by
  have hP2 : Topology.P2 A := P2_of_dense_interior (X := X) (A := A) hA
  exact P2_implies_P3 hP2