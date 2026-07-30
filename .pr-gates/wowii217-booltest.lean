import FormalConjecturesUtil

def boolAt14
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : Bool) : Nat → Bool
  | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4 | 5 => b5 | 6 => b6
  | 7 => b7 | 8 => b8 | 9 => b9 | 10 => b10 | 11 => b11 | 12 => b12 | _ => b13

theorem test :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : Bool,
      (b0 || b1 || b2 || b3 || b4 || b5 || b6 || b7 || b8 || b9 || b10 ||
        b11 || b12 || b13) = true →
      ∃ v : Fin 14, boolAt14 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 v = true := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 h
  simp only [Bool.or_eq_true] at h
  rcases h with ((((((((((((h0 | h1) | h2) | h3) | h4) | h5) | h6) | h7) |
    h8) | h9) | h10) | h11) | h12) | h13
  · exact ⟨0, h0⟩
  · exact ⟨1, h1⟩
  · exact ⟨2, h2⟩
  · exact ⟨3, h3⟩
  · exact ⟨4, h4⟩
  · exact ⟨5, h5⟩
  · exact ⟨6, h6⟩
  · exact ⟨7, h7⟩
  · exact ⟨8, h8⟩
  · exact ⟨9, h9⟩
  · exact ⟨10, h10⟩
  · exact ⟨11, h11⟩
  · exact ⟨12, h12⟩
  · exact ⟨13, h13⟩
