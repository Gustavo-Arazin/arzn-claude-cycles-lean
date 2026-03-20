import ClaudeCyclesARZN.Core

namespace ClaudeCyclesARZN

inductive LocalPerm where
  | p012
  | p021
  | p102
  | p120
  | p201
  | p210
  deriving DecidableEq, Repr, Inhabited

def LocalPerm.toString : LocalPerm → String
  | .p012 => "012"
  | .p021 => "021"
  | .p102 => "102"
  | .p120 => "120"
  | .p201 => "201"
  | .p210 => "210"

def admissibleEvenM (m : Nat) : Prop :=
  8 ≤ m ∧ m % 2 = 0

def half (m : Nat) : Nat :=
  m / 2

def fiberSum (m i j k : Nat) : Nat :=
  (i + j + k) % m

def tauLayerCode (m i j : Nat) : LocalPerm :=
  let h := half m
  if i = 0 then
    if j = m - 2 then .p210
    else if j = m - 1 then .p102
    else .p012
  else if i = 1 then
    if j = m - 2 then .p201
    else if j = m - 1 then .p210
    else .p012
  else if 2 ≤ i ∧ i ≤ h - 3 then
    if j = m - 1 - i then .p102
    else if j = m - 1 then .p210
    else .p012
  else if i = h - 2 then
    if j ≤ h then .p021
    else if j = h + 1 then .p120
    else if j = m - 2 then
      if m % 4 = 0 then .p012 else .p102
    else if j = m - 1 then
      if m % 4 = 0 then .p201 else .p021
    else .p012
  else if i = h - 1 then
    if j ≤ h - 1 then .p021
    else if j = h then .p120
    else if h + 1 ≤ j ∧ j ≤ m - 3 then .p021
    else if j = m - 2 then
      if m % 4 = 0 then .p021 else .p201
    else if j = m - 1 then
      if m % 4 = 0 then .p201 else .p021
    else .p021
  else if i = h then
    if j ≤ h - 2 then .p021
    else if j = h - 1 then .p120
    else if h ≤ j ∧ j ≤ m - 3 then .p021
    else if j = m - 2 then
      if m % 4 = 0 then .p021 else .p201
    else if j = m - 1 then
      if m % 4 = 0 then .p201 else .p021
    else .p021
  else if i = h + 1 then
    if j ≤ h - 3 then .p012
    else if j = h - 2 then .p102
    else if h - 1 ≤ j ∧ j ≤ m - 3 then .p021
    else if j = m - 2 then
      if m % 4 = 0 then .p120 else .p210
    else if j = m - 1 then .p012
    else .p012
  else if h + 2 ≤ i ∧ i ≤ m - 1 then
    if j = m - 1 - i then .p102
    else if j = m - 2 then .p210
    else .p012
  else
    .p012

def evenRuleCode (m i j k : Nat) : LocalPerm :=
  let s := fiberSum m i j k
  let h := half m
  if s ≤ m - 3 then .p012
  else if s = m - 1 then
    if i = h - 1 ∨ i = h then .p210 else .p120
  else if s = m - 2 then
    tauLayerCode m i j
  else
    .p012

def isExceptionalFiber (m s : Nat) : Bool :=
  s = m - 2 || s = m - 1

def evenRuleSummary (m i j k : Nat) : String :=
  s!"m={m}, i={i}, j={j}, k={k}, s={fiberSum m i j k}, code={LocalPerm.toString (evenRuleCode m i j k)}"

end ClaudeCyclesARZN
