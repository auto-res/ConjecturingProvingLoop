

theorem interior_closure_prod_nonempty_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    (interior (closure (A ×ˢ B))).Nonempty ↔
      ((interior (closure A)).Nonempty ∧ (interior (closure B)).Nonempty) := by
  have hEq :=
    interior_closure_prod (X := X) (Y := Y) (A := A) (B := B)
  constructor
  · intro hProd
    rcases hProd with ⟨p, hp⟩
    have hp' :
        (p : X × Y) ∈ interior (closure A) ×ˢ interior (closure B) := by
      simpa [hEq] using hp
    rcases hp' with ⟨hpA, hpB⟩
    exact ⟨⟨p.1, hpA⟩, ⟨p.2, hpB⟩⟩
  · rintro ⟨hIntA, hIntB⟩
    rcases hIntA with ⟨x, hx⟩
    rcases hIntB with ⟨y, hy⟩
    have hp :
        ((x, y) : X × Y) ∈
          interior (closure A) ×ˢ interior (closure B) :=
      And.intro hx hy
    have hpProd :
        ((x, y) : X × Y) ∈ interior (closure (A ×ˢ B)) := by
      simpa [hEq] using hp
    exact ⟨(x, y), hpProd⟩