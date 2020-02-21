-- Math 52: Quiz 3
-- Open this file in a folder that contains 'utils'.

import utils.int_refl

definition is_even (n : ℤ) : Prop := ∃ (k : ℤ), n = 2 * k

definition is_odd (n : ℤ) : Prop := ∃ (k : ℤ), n = 2 * k + 1

axiom even_or_odd (n : ℤ) : is_even n ∨ is_odd n

theorem main : ∀ (n : ℤ), is_even (n * n + 3 * n + 2) :=
begin
intro n,
have H := even_or_odd n,
cases H,
{ unfold is_even at H,  
  unfold is_even,
  cases H with i Hi,
  existsi (2 * i * i + 3 * i + 1 : ℤ),
  rw Hi,
  int_refl [i],
},
{ unfold is_odd at H,
  unfold is_even,
  cases H with j Hj,
  existsi (2 * j * j + 5 * j + 3 : ℤ),
  rw Hj,
  int_refl [j],
},
end
