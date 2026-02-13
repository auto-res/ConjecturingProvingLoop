

theorem P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A := by
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  exact subset_closure hx_int

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (Set.prod A B) := by
  intro x hx
  rcases x with ⟨a, b⟩
  rcases hx with ⟨ha, hb⟩
  have ha' : a ∈ interior (closure (interior A)) := hA ha
  have hb' : b ∈ interior (closure (interior B)) := hB hb
  have : (a, b) ∈ interior (closure (interior (A ×ˢ B))) := by
    simpa [interior_prod_eq, closure_prod_eq] using And.intro ha' hb'
  exact this

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P3 A) (hB : Topology.P3 B) : Topology.P3 (Set.prod A B) := by
  intro x hx
  rcases x with ⟨a, b⟩
  rcases hx with ⟨ha, hb⟩
  have ha' : a ∈ interior (closure A) := hA ha
  have hb' : b ∈ interior (closure B) := hB hb
  have hmem : (a, b) ∈ interior (closure (A ×ˢ B)) := by
    -- rewrite via `closure_prod_eq` and `interior_prod_eq`
    have : (a, b) ∈ (interior (closure A) ×ˢ interior (closure B)) := by
      exact ⟨ha', hb'⟩
    simpa [closure_prod_eq, interior_prod_eq] using this
  exact hmem