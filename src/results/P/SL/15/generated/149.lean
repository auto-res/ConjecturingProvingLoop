

theorem P3_prod_left_of_nonempty
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hBne : B.Nonempty) :
    Topology.P3 (A ×ˢ B) → Topology.P3 A := by
  intro hProd
  dsimp [Topology.P3] at hProd
  dsimp [Topology.P3]
  intro x hxA
  rcases hBne with ⟨y, hyB⟩
  have h_mem_prod : ((x, y) : X × Y) ∈ A ×ˢ B := by
    exact And.intro hxA hyB
  have hIntProd : ((x, y) : X × Y) ∈ interior (closure (A ×ˢ B)) :=
    hProd h_mem_prod
  have h_closure_prod :
      closure (A ×ˢ B) = (closure A) ×ˢ (closure B) := by
    simpa using closure_prod_eq (s := A) (t := B)
  have hIntProd' :
      ((x, y) : X × Y) ∈ interior ((closure A) ×ˢ (closure B)) := by
    simpa [h_closure_prod] using hIntProd
  have h_int_prod_eq :
      interior ((closure A) ×ˢ (closure B)) =
        interior (closure A) ×ˢ interior (closure B) := by
    simpa using interior_prod_eq (s := closure A) (t := closure B)
  have hMem :
      ((x, y) : X × Y) ∈ interior (closure A) ×ˢ interior (closure B) := by
    simpa [h_int_prod_eq] using hIntProd'
  exact (Set.mem_prod.1 hMem).1