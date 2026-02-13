

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P3 A → P3 B → P3 (Set.prod A B) := by
  intro hP3A hP3B
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- each coordinate enjoys `P3`
  have hA : p.1 ∈ interior (closure A) := hP3A hpA
  have hB : p.2 ∈ interior (closure B) := hP3B hpB
  -- neighbourhoods around each coordinate
  set U : Set X := interior (closure A) with hU
  set V : Set Y := interior (closure B) with hV
  have hU_open : IsOpen U := by
    simpa [hU] using isOpen_interior
  have hV_open : IsOpen V := by
    simpa [hV] using isOpen_interior
  -- open neighbourhood of `p`
  have hUV_open : IsOpen (U ×ˢ V) := hU_open.prod hV_open
  have hpUV : p ∈ U ×ˢ V := by
    have hpU : p.1 ∈ U := by
      simpa [hU] using hA
    have hpV : p.2 ∈ V := by
      simpa [hV] using hB
    exact ⟨hpU, hpV⟩
  -- show this neighbourhood is contained in the closure
  have h_sub : (U ×ˢ V) ⊆ closure (Set.prod A B) := by
    intro q hq
    rcases hq with ⟨hqU, hqV⟩
    have hq1 : q.1 ∈ closure A := interior_subset hqU
    have hq2 : q.2 ∈ closure B := interior_subset hqV
    have hq_prod : q ∈ (closure A) ×ˢ (closure B) := ⟨hq1, hq2⟩
    have h_cl_eq : closure (Set.prod A B) = (closure A) ×ˢ (closure B) := by
      simpa using closure_prod_eq
    simpa [h_cl_eq] using hq_prod
  -- hence it lies in the interior of the closure
  have h_into : (U ×ˢ V) ⊆ interior (closure (Set.prod A B)) :=
    interior_maximal h_sub hUV_open
  exact h_into hpUV

theorem P2_symm_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set Y} (e : X ≃ₜ Y) : P2 (e.symm '' A) ↔ P2 A := by
  constructor
  · intro hP2
    -- First transport the property along `e`.
    have h : P2 (e '' (e.symm '' A)) :=
      (P2_image_homeomorph (e := e) (A := e.symm '' A)) hP2
    -- Identify the transported set with `A`.
    have hset : (e '' (e.symm '' A) : Set Y) = A := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨x, hx, rfl⟩
        rcases hx with ⟨z, hzA, rfl⟩
        simpa [e.apply_symm_apply] using hzA
      · intro hyA
        exact ⟨e.symm y, ⟨y, hyA, rfl⟩, by
          simp⟩
    simpa [hset] using h
  · intro hP2A
    simpa using
      (P2_image_homeomorph (e := e.symm) (A := A)) hP2A

theorem P3_conv_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} : closure A = Set.univ → P3 (closure A) := by
  intro h_dense
  -- The closure of `closure A` is still `closure A`, hence also `univ`.
  have h_dense' : closure (closure A) = (Set.univ : Set X) := by
    simpa [closure_closure] using h_dense
  -- Apply the existing lemma for dense sets.
  have hP3 : P3 (closure A) := P3_of_dense (A := closure A) h_dense'
  simpa using hP3