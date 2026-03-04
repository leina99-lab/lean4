# Lean4 완전 정복 가이드 —  Part 11-B: 선형 점화 관계 풀기 (Solving Linear Recurrence Relations)

> **Rosen 이산수학 8판 · Section 8.1 (동적 프로그래밍) + 8.2 기반**
> 『Mathematics in Lean』 + Lean 4 공식화

---

## 0. 들어가며

Part 11-A에서는 점화 관계의 기본 개념과 피보나치, 하노이 탑을 다루었다. 이번 Part 11-B에서는 더 깊이 들어간다:

1. **선형 동차 점화 관계**(linear homogeneous recurrence relation)의 정의
2. **특성 방정식**(characteristic equation)으로 일반항 구하기
3. **선형 비동차 점화 관계**(linear nonhomogeneous recurrence relation)
4. **동적 프로그래밍**(dynamic programming)의 점화 관계
5. Lean 4에서 **꼬리 재귀**(tail recursion)로 효율적 구현하기

### 이 파트에서 새로 등장하는 Lean 4 개념

| 개념 | 설명 |
|------|------|
| `where` 절 | 보조 함수를 정의 안에 포함 |
| `generalizing` | 귀납 가정을 일반화 |
| `erw` | 확장 재작성 (정의 펼침에 더 적극적) |
| `Nat.strongRecOn` | 강한 귀납법 |
| `calc` | 계산 체인 |

---

## 1. 선형 동차 점화 관계

### 1.1 정의

> **정의**: **상수 계수를 갖는 k차의 선형 동차 점화 관계**(linear homogeneous recurrence relation with constant coefficients of degree k)는 다음과 같은 형태를 갖는 점화 관계이다:
>
> `aₙ = c₁·aₙ₋₁ + c₂·aₙ₋₂ + ⋯ + cₖ·aₙ₋ₖ`
>
> 여기서 `c₁, c₂, ..., cₖ`는 실수이고 `cₖ ≠ 0`이다.

용어를 하나씩 뜯어보자:

- **선형**(linear): 오른쪽이 이전 항들의 **배수의 합**이다. `aₙ₋₁²` 같은 제곱항이 없다.
- **동차**(homogeneous): `aₙ`의 배수가 아닌 항(상수항 등)이 없다. 즉, 모든 항이 `a`의 배수이다.
- **상수 계수**(constant coefficients): `c₁, c₂, ...`가 `n`에 의존하지 않는 고정된 수이다.
- **k차**(degree k): `aₙ`이 `k`개 이전 항까지 참조한다.

### 1.2 예시

| 점화 관계 | 선형? | 동차? | 상수 계수? | 차수 |
|-----------|------|------|----------|------|
| `aₙ = aₙ₋₁ + aₙ₋₂` (피보나치) | ✅ | ✅ | ✅ | 2 |
| `Hₙ = 2Hₙ₋₁ + 1` (하노이) | ✅ | ❌ (+1이 있음) | ✅ | 1 |
| `aₙ = aₙ₋₁ + aₙ₋₂²` | ❌ (제곱) | — | — | — |
| `aₙ = n·aₙ₋₁` (팩토리얼) | ✅ | ✅ | ❌ (n이 변함) | 1 |

### 1.3 Lean 4에서의 인식

Lean 4에서 선형 동차 점화 관계는 자연스럽게 재귀 함수로 표현된다:

```lean
-- 1차 선형 동차: aₙ = c·aₙ₋₁
-- 예: 인구가 매년 c배로 늘어나는 모델
def linearRecur1 (c : ℕ) (a₀ : ℕ) : ℕ → ℕ
  | 0     => a₀
  | n + 1 => c * linearRecur1 c a₀ n

-- 2차 선형 동차: aₙ = c₁·aₙ₋₁ + c₂·aₙ₋₂
-- 피보나치는 c₁ = 1, c₂ = 1인 특수 경우
def linearRecur2 (c₁ c₂ : ℕ) (a₀ a₁ : ℕ) : ℕ → ℕ
  | 0     => a₀
  | 1     => a₁
  | n + 2 => c₁ * linearRecur2 c₁ c₂ a₀ a₁ (n + 1) +
             c₂ * linearRecur2 c₁ c₂ a₀ a₁ n
```

---

## 2. 특성 방정식 — 점화 관계를 푸는 열쇠

### 2.1 아이디어

2차 선형 동차 점화 관계 `aₙ = c₁·aₙ₋₁ + c₂·aₙ₋₂`를 풀고 싶다.

핵심 아이디어: **`aₙ = rⁿ` 형태의 해를 찾자!**

`aₙ = rⁿ`을 점화 관계에 대입하면:

```
rⁿ = c₁·rⁿ⁻¹ + c₂·rⁿ⁻²
```

양변을 `rⁿ⁻²`로 나누면:

```
r² = c₁·r + c₂
```

즉: **r² - c₁·r - c₂ = 0**

이것이 바로 **특성 방정식**(characteristic equation)이다!

### 2.2 Rosen 정리 1: 두 개의 서로 다른 특성근

> **정리 1** (Rosen 8.2 정리 1):
> `c₁`과 `c₂`는 실수라 하자. `r² - c₁r - c₂ = 0`이 두 개의 서로 다른 근 `r₁`과 `r₂`를 갖는다고 가정하자.
> 그러면 수열 `{aₙ}`이 점화 관계 `aₙ = c₁·aₙ₋₁ + c₂·aₙ₋₂`의 해라는 것은 
> `α₁`과 `α₂`가 상수일 때 `aₙ = α₁·r₁ⁿ + α₂·r₂ⁿ`이라는 것과 동치이다.

**이것이 말하는 바**: 특성 방정식의 두 근 `r₁, r₂`를 찾으면, 일반항은 반드시 `α₁·r₁ⁿ + α₂·r₂ⁿ` 형태이다. 초기조건에서 `α₁, α₂`를 구하면 끝!

### 2.3 예제: aₙ = aₙ₋₁ + 2·aₙ₋₂ 풀기

**문제** (Rosen 예제 3): 초기조건 `a₀ = 2`, `a₁ = 7`인 점화 관계 `aₙ = aₙ₋₁ + 2·aₙ₋₂`의 해를 구하라.

**풀이**:

1. **특성 방정식**: `r² - r - 2 = 0`
2. **인수분해**: `(r - 2)(r + 1) = 0`
3. **특성근**: `r₁ = 2`, `r₂ = -1`
4. **일반항**: `aₙ = α₁·2ⁿ + α₂·(-1)ⁿ`
5. **초기조건 대입**:
   - `a₀ = 2`: `α₁ + α₂ = 2`
   - `a₁ = 7`: `2α₁ - α₂ = 7`
6. **연립방정식 풀기**: `α₁ = 3`, `α₂ = -1`
7. **답**: `aₙ = 3·2ⁿ - (-1)ⁿ`

### 2.4 Lean 4에서 검증

특성 방정식을 직접 풀기보다, Lean 4에서는 **닫힌 공식이 맞는지 검증**하는 것이 더 자연스럽다:

```lean
-- Rosen 예제 3의 점화 관계
def rosen83 : ℕ → ℤ  -- 정수(ℤ)를 사용한다: (-1)ⁿ 때문
  | 0     => 2
  | 1     => 7
  | n + 2 => rosen83 (n + 1) + 2 * rosen83 n

-- 처음 몇 항 확인
#eval List.range 8 |>.map rosen83
-- [2, 7, 11, 25, 47, 97, 191, 385]

-- 닫힌 공식으로 계산한 값과 비교
-- 3·2ⁿ - (-1)ⁿ
-- n=0: 3·1 - 1 = 2 ✓
-- n=1: 3·2 - (-1) = 7 ✓
-- n=2: 3·4 - 1 = 11 ✓
-- n=3: 3·8 - (-1) = 25 ✓
```

---

## 3. 피보나치의 명시적 공식 (Binet's Formula)

### 3.1 특성 방정식으로부터

피보나치 점화 관계 `fₙ = fₙ₋₁ + fₙ₋₂`의 특성 방정식은:

```
r² - r - 1 = 0
```

근의 공식으로:
```
r₁ = (1 + √5) / 2 = φ    (황금비, golden ratio)
r₂ = (1 - √5) / 2 = φ'   (황금비의 켤레)
```

따라서 일반항: `fₙ = α₁·φⁿ + α₂·(φ')ⁿ`

초기조건 `f₀ = 0`, `f₁ = 1`에서: `α₁ = 1/√5`, `α₂ = -1/√5`

**비네 공식**(Binet's formula):

```
fₙ = (φⁿ - (φ')ⁿ) / √5
```

### 3.2 Lean 4에서의 비네 공식

Mathematics in Lean에 나온 증명을 살펴보자. 이 증명은 실수 위에서 진행되므로 `noncomputable`이 필요하다:

```lean
noncomputable section

-- 황금비와 켤레
def phi : ℝ := (1 + Real.sqrt 5) / 2
def phi' : ℝ := (1 - Real.sqrt 5) / 2

-- 핵심 보조정리: φ² = φ + 1
theorem phi_sq : phi ^ 2 = phi + 1 := by
  field_simp [phi, add_sq]; ring

-- 핵심 보조정리: (φ')² = φ' + 1
theorem phi'_sq : phi' ^ 2 = phi' + 1 := by
  field_simp [phi', sub_sq]; ring

-- 비네 공식: fib n = (φⁿ - (φ')ⁿ) / √5
theorem fib_eq : ∀ n, (fib n : ℝ) = (phi ^ n - phi' ^ n) / Real.sqrt 5
  | 0     => by simp
  | 1     => by field_simp [phi, phi']
  | n + 2 => by field_simp [fib_eq, pow_add, phi_sq, phi'_sq]; ring

end
```

**증명 구조 해설**:

1. 이 증명은 `induction`이 아니라 **재귀 함수 스타일**로 작성되었다. Lean 4에서는 정리도 재귀 함수처럼 정의할 수 있다!
2. 기저 사례 (n = 0, 1)은 대수적 계산으로 처리한다.
3. 귀납 단계 (n + 2)에서는 `fib_eq n`과 `fib_eq (n + 1)`을 재귀적으로 사용한다.
4. `field_simp`는 분수를 정리하고, `ring`은 대수적 항등식을 자동 증명한다.

---

## 4. 꼬리 재귀: 효율적인 피보나치 구현

### 4.1 문제: 단순 재귀의 비효율성

위에서 정의한 `fib`은 **지수 시간**(exponential time)이 걸린다! `fib 40`만 해도 엄청 느리다.

왜? `fib (n + 2) = fib n + fib (n + 1)`에서 `fib n`과 `fib (n + 1)`을 각각 계산하는데, 이 과정에서 같은 값을 반복 계산하기 때문이다.

### 4.2 해결: 꼬리 재귀

**꼬리 재귀**(tail recursion)란 재귀 호출이 함수의 **마지막 연산**인 경우이다. 이 경우 컴파일러가 루프로 변환할 수 있어 효율적이다.

```lean
-- 꼬리 재귀 피보나치: O(n) 시간
def fib' (n : Nat) : Nat :=
  aux n 0 1
where aux        -- where 절: 보조 함수를 정의 내부에 포함
  | 0, x, _     => x            -- n = 0이면 첫 번째 인수 반환
  | n + 1, x, y => aux n y (x + y)  -- 한 칸 전진: (x, y) → (y, x+y)
```

이 `where` 절을 이해해보자:

- `aux n x y`는 "현재 카운트다운 n, 현재 fib 값 x, 다음 fib 값 y"를 뜻한다.
- `aux 0 x _`이면 x를 반환한다.
- `aux (n+1) x y`이면 `aux n y (x+y)`로 한 단계 전진한다.

**실행 추적**:
```
fib' 5
= aux 5 0 1
= aux 4 1 1
= aux 3 1 2
= aux 2 2 3
= aux 1 3 5
= aux 0 5 8
= 5
```

```lean
-- 꼬리 재귀 버전은 엄청 빠르다!
#eval fib' 10000  -- 즉시 계산됨 (fib 10000은 2000자리 이상!)
```

### 4.3 동치성 증명

꼬리 재귀 버전이 원래 정의와 같은 값을 계산함을 증명해야 한다:

```lean
-- 보조 함수의 성질
theorem fib'.aux_eq (m n : ℕ) :
    fib'.aux n (fib m) (fib (m + 1)) = fib (n + m) := by
  induction n generalizing m with
  | zero => simp [fib'.aux]
  | succ n ih => rw [fib'.aux, ← fib_add_two, ih, add_assoc, add_comm 1]

-- 최종 동치성
theorem fib'_eq_fib : fib' = fib := by
  ext n
  erw [fib', fib'.aux_eq 0 n]; rfl
```

**핵심 포인트들**:

1. `generalizing m` — 귀납 가정에서 `m`이 **모든 m에 대해** 성립하게 만든다. 이렇게 해야 귀납 단계에서 `m` 대신 `m + 1`을 사용할 수 있다.

2. `erw` — "확장 재작성"(extended rewrite). 일반 `rw`보다 더 적극적으로 정의를 펼친다. `fib 0`을 `0`으로, `fib 1`을 `1`로 환원하는 데 필요하다.

---

## 5. 동적 프로그래밍과 점화 관계

### 5.1 기억화(Memoization)

**동적 프로그래밍**(dynamic programming)의 핵심은 **기억화**(memoization)이다. 즉, 이미 계산한 값을 저장해두고 재사용하는 것이다.

이것은 점화 관계와 자연스럽게 연결된다: 점화 관계를 "아래에서 위로"(bottom-up) 계산하면 각 값을 한 번만 계산하면 된다.

### 5.2 계단 오르기 문제

**문제** (Rosen 연습문제 11): 한 사람이 한 번에 한 계단 또는 두 계단을 오를 때, n 계단을 오르는 방법의 수에 대한 점화 관계를 구하라.

**분석**: `sₙ`을 n 계단을 오르는 방법의 수라 하자.
- 마지막에 한 계단 올랐다면, 그 전에 n-1 계단을 올라야 한다 → `sₙ₋₁`가지
- 마지막에 두 계단 올랐다면, 그 전에 n-2 계단을 올라야 한다 → `sₙ₋₂`가지

따라서: `sₙ = sₙ₋₁ + sₙ₋₂` (피보나치와 같은 구조!)

초기조건: `s₁ = 1` (1칸), `s₂ = 2` (1+1 또는 2)

```lean
-- 계단 오르기 문제
def stairClimb : ℕ → ℕ
  | 0     => 1    -- 0 계단: 아무것도 안 하는 방법 1가지
  | 1     => 1    -- 1 계단: 한 칸 오르기
  | n + 2 => stairClimb (n + 1) + stairClimb n

#eval List.range 10 |>.map stairClimb
-- [1, 1, 2, 3, 5, 8, 13, 21, 34, 55]
-- 피보나치 수열과 동일하다!
```

### 5.3 계단 문제의 피보나치 관계 증명

```lean
-- stairClimb n = fib (n + 1) 임을 증명
theorem stairClimb_eq_fib (n : ℕ) : stairClimb n = fib (n + 1) := by
  induction n with
  | zero => simp [stairClimb, fib]
  | succ n ih =>
    cases n with
    | zero => simp [stairClimb, fib]
    | succ n =>
      simp only [stairClimb, fib]
      -- stairClimb (n + 2) + stairClimb (n + 1) = fib (n + 2) + fib (n + 3)
      -- 이것은 귀납 가정과 이전 단계의 결과를 사용한다
      sorry -- 완전한 증명은 연습 문제로!
```

---

## 6. 연습 문제 — 레벨 1: 괄호 채우기

### 연습 6.1: 1차 선형 점화 관계 정의

```lean
-- 수열: 1, 3, 9, 27, 81, ... (3의 거듭제곱)
-- 점화 관계: aₙ₊₁ = 3·aₙ, a₀ = 1
def tripling : ℕ → ℕ
  | 0     => {① 초기값}
  | n + 1 => {② 점화 관계}
```

<details>
<summary>💡 답 보기</summary>

```lean
def tripling : ℕ → ℕ
  | 0     => 1               -- ① 3⁰ = 1
  | n + 1 => 3 * tripling n  -- ② aₙ₊₁ = 3·aₙ
```
</details>

### 연습 6.2: 2차 선형 점화 관계 정의

```lean
-- 루카스 수열(Lucas sequence): Lₙ = Lₙ₋₁ + Lₙ₋₂
-- 피보나치와 같은 점화 관계이지만 초기값이 다르다!
-- L₀ = 2, L₁ = 1
def lucas : ℕ → ℕ
  | 0     => {③ 초기값 1}
  | 1     => {④ 초기값 2}
  | n + 2 => {⑤ 점화 관계}

-- 검증: 처음 몇 항은 2, 1, 3, 4, 7, 11, 18, 29, ...
-- #eval List.range 10 |>.map lucas
```

<details>
<summary>💡 답 보기</summary>

```lean
def lucas : ℕ → ℕ
  | 0     => 2                       -- ③ L₀ = 2
  | 1     => 1                       -- ④ L₁ = 1
  | n + 2 => lucas (n + 1) + lucas n -- ⑤ Lₙ₊₂ = Lₙ₊₁ + Lₙ
```
</details>

### 연습 6.3: 귀납법 기저 사례

```lean
-- tripling n = 3^n 증명의 기저 사례를 완성하라
theorem tripling_eq (n : ℕ) : tripling n = 3 ^ n := by
  induction n with
  | zero =>
    {⑥ 기저 사례: tripling 0 = 3^0}
  | succ n ih =>
    simp [tripling]
    rw [ih]
    ring
```

<details>
<summary>💡 답 보기</summary>

```lean
  | zero =>
    simp [tripling]  -- ⑥ tripling 0 = 1 = 3^0
```
</details>

---

## 7. 연습 문제 — 레벨 2: skeleton 채우기

### 연습 7.1: 하노이 탑 변형 — 3칸 계단 오르기

```lean
-- 한 번에 1, 2, 또는 3 계단을 오를 수 있을 때
-- n 계단을 오르는 방법의 수
def stairClimb3 : ℕ → ℕ
  | 0     => 1
  | 1     => 1
  | 2     => 2    -- 1+1, 2
  | n + 3 => stairClimb3 (n + 2) + stairClimb3 (n + 1) + stairClimb3 n

-- 값 확인: 1, 1, 2, 4, 7, 13, 24, 44, ...
-- #eval List.range 10 |>.map stairClimb3

-- stairClimb3 8 의 값을 구하라
example : stairClimb3 8 = {⑦ 값} := by {⑧ 전술}
```

<details>
<summary>💡 답 보기</summary>

```lean
example : stairClimb3 8 = 81 := by native_decide
-- 확인: 1, 1, 2, 4, 7, 13, 24, 44, 81
```
</details>

### 연습 7.2: 코드단어 수 (Rosen 예제 4)

**문제**: 짝수 개의 0을 포함하는 10진수 문자열을 유효하다고 한다. 유효한 n-자리 코드단어의 수 `aₙ`에 대한 점화 관계를 구하라.

**분석**: `aₙ = 8·aₙ₋₁ + 10ⁿ⁻¹`

```lean
-- 유효한 n자리 코드단어의 수
-- aₙ = 8·aₙ₋₁ + 10^(n-1)
-- a₁ = 9 (0이 아닌 한 자리: 1~9)
def validCodes : ℕ → ℕ
  | 0     => 1     -- 빈 문자열 (관례)
  | 1     => 9
  | n + 1 => 8 * validCodes n + 10 ^ n

-- 처음 몇 항
-- #eval List.range 6 |>.map validCodes

-- validCodes 2의 값을 구하라
-- a₂ = 8·9 + 10 = 72 + 10 = 82
example : validCodes 2 = {⑨ 값} := by {⑩ 전술}
```

<details>
<summary>💡 답 보기</summary>

```lean
example : validCodes 2 = 82 := by native_decide
```
</details>

### 연습 7.3: 꼬리 재귀 하노이

```lean
-- 하노이 탑의 꼬리 재귀 버전을 작성하라
def hanoi' (n : Nat) : Nat :=
  aux n 0
where aux
  | 0, acc     => acc
  | n + 1, acc => {⑪ 재귀 호출}

-- 검증
-- #eval hanoi' 10  -- 1023
-- #eval hanoi' 20  -- 1048575
```

<details>
<summary>💡 답 보기</summary>

```lean
def hanoi' (n : Nat) : Nat :=
  aux n 0
where aux
  | 0, acc     => acc
  | n + 1, acc => aux n (2 * acc + 1)  -- ⑪ Hₙ₊₁ = 2·Hₙ + 1

-- acc는 "지금까지의 누적값"이다
-- aux n acc 는 "n단계 남았고 현재 누적 이동 횟수가 acc"라는 뜻
-- 한 단계 줄이면: acc' = 2*acc + 1
```
</details>

---

## 8. 연습 문제 — 레벨 3: sorry 채우기 (독립 증명)

### 연습 8.1: 루카스 수열의 성질

```lean
-- 루카스 수열은 lucas (n+1) = fib n + fib (n+2) 를 만족한다
-- (이것은 fib과 lucas의 아름다운 관계이다)

-- 먼저 쉬운 것부터: lucas 값 확인
example : lucas 5 = 11 := by sorry

-- 루카스-피보나치 관계 (처음 몇 값으로 확인)
example : lucas 3 = fib 2 + fib 4 := by sorry
example : lucas 4 = fib 3 + fib 5 := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : lucas 5 = 11 := by native_decide
example : lucas 3 = fib 2 + fib 4 := by native_decide
example : lucas 4 = fib 3 + fib 5 := by native_decide
```
</details>

### 연습 8.2: 합 공식

```lean
-- 처음 n개의 자연수의 합: 1 + 2 + ... + n = n(n+1)/2
-- 점화 관계: sₙ = sₙ₋₁ + n
def sumTo : ℕ → ℕ
  | 0     => 0
  | n + 1 => sumTo n + (n + 1)

-- sumTo n = n * (n + 1) / 2 를 증명하라
-- 뺄셈/나눗셈 없이 양변에 2를 곱한 형태로 증명하는 것이 더 쉽다
theorem sumTo_formula (n : ℕ) : 2 * sumTo n = n * (n + 1) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem sumTo_formula (n : ℕ) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    simp [sumTo]
    -- 목표: 2 * (sumTo n + (n + 1)) = (n + 1) * (n + 2)
    -- 2 * sumTo n + 2 * (n + 1) = (n + 1) * (n + 2)
    -- ih에서 2 * sumTo n = n * (n + 1) 이므로
    -- n * (n + 1) + 2 * (n + 1) = (n + 1) * (n + 2)
    -- (n + 2) * (n + 1) = (n + 1) * (n + 2) ✓
    ring_nf
    omega
```

**또는 더 간결하게:**

```lean
theorem sumTo_formula (n : ℕ) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    simp [sumTo]; linarith
```
</details>

### 연습 8.3: 피보나치 항등식 (도전!)

Mathematics in Lean에서 나온 문제이다.

```lean
-- fib_add: fib (m + n + 1) = fib m * fib n + fib (m+1) * fib (n+1)
-- 이것을 사용하여 다음을 증명하라:
-- (fib n)² + (fib (n+1))² = fib (2n + 1)

example (n : ℕ) : (fib n) ^ 2 + (fib (n + 1)) ^ 2 = fib (2 * n + 1) := by
  sorry
```

<details>
<summary>💡 힌트</summary>

`fib_add`를 `m = n`, `n = n`으로 적용한다. 그러면 `fib (n + n + 1) = fib n * fib n + fib (n+1) * fib (n+1)`이 되고, 이는 곧 `fib (2n + 1) = (fib n)² + (fib (n+1))²`이다.
</details>

<details>
<summary>💡 답 보기</summary>

```lean
-- fib_add가 Mathlib에 있다고 가정
-- fib_add (m n : ℕ) : fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1)

example (n : ℕ) : (fib n) ^ 2 + (fib (n + 1)) ^ 2 = fib (2 * n + 1) := by
  have h := fib_add n n
  -- h : fib (n + n + 1) = fib n * fib n + fib (n+1) * fib (n+1)
  rw [show n + n = 2 * n from by ring] at h
  rw [sq, sq]
  linarith
```
</details>

---

## 9. 비동차 점화 관계 맛보기

### 9.1 정의

**선형 비동차 점화 관계**(linear nonhomogeneous recurrence relation)는 다음 형태이다:

`aₙ = c₁·aₙ₋₁ + c₂·aₙ₋₂ + ⋯ + cₖ·aₙ₋ₖ + F(n)`

여기서 `F(n)`은 n에 의존하는 함수로, 0이 아니다.

**예**: 하노이 탑 `Hₙ = 2Hₙ₋₁ + 1`에서 `F(n) = 1`이다.

### 9.2 Rosen 정리 5: 비동차 = 동차의 해 + 특수해

> **정리 5**: 비동차 점화 관계의 **모든** 해는 다음과 같이 표현된다:
>
> `aₙ = aₙ⁽ᵖ⁾ + aₙ⁽ʰ⁾`
>
> 여기서 `aₙ⁽ᵖ⁾`는 비동차 관계의 **특수해**(particular solution)이고, `aₙ⁽ʰ⁾`는 연관된 동차 관계의 **일반해**(homogeneous solution)이다.

비유: 비동차 관계의 해는 "기본 흐름(동차의 해)" + "외부 영향(특수해)"이다.

### 9.3 예제: aₙ = 3·aₙ₋₁ + 2n (Rosen 예제 10)

```lean
-- Rosen 예제 10: aₙ = 3·aₙ₋₁ + 2n, a₁ = 3
-- 연관 동차: aₙ = 3·aₙ₋₁ → 해: α·3ⁿ
-- F(n) = 2n이므로 특수해를 pₙ = cn + d로 추측
-- 대입: cn + d = 3(c(n-1) + d) + 2n
-- cn + d = 3cn - 3c + 3d + 2n
-- (2 + 2c)n + (2d - 3c) = 0
-- c = -1, d = -3/2
-- 특수해: aₙ⁽ᵖ⁾ = -n - 3/2
-- 일반해: aₙ = -n - 3/2 + α·3ⁿ

-- Lean 4에서는 자연수 범위에서 직접 검증하는 것이 더 자연스럽다
def rosen810 : ℕ → ℤ  -- 정수 사용
  | 0     => 0   -- 편의상 a₀ = 0으로 설정
  | n + 1 => 3 * rosen810 n + 2 * (n + 1 : ℤ)

#eval List.range 8 |>.map rosen810
-- [0, 2, 10, 38, 124, ...]
```

---

## 10. 사용된 Lean 4 전술 · 함수 정리

### 새로 배운 전술

| 전술 | 용도 | 예시 |
|------|------|------|
| `generalizing x` | 귀납 가정 일반화 | `induction n generalizing m` |
| `erw` | 확장 재작성 | 정의 환원이 필요할 때 |
| `field_simp` | 분수 정리 | 실수 분수 계산 |
| `ring_nf` | ring 정규화 | ring보다 유연함 |
| `linarith` | 선형 부등식 | `linarith [ih]` |

### 새로 배운 함수/개념

| 개념 | 설명 |
|------|------|
| `where` 절 | `def f n := aux n 0 where aux ...` |
| 꼬리 재귀 | 마지막 연산이 재귀 호출 → O(n) |
| 특성 방정식 | `r² - c₁r - c₂ = 0` |
| 비네 공식 | `fib n = (φⁿ - ψⁿ) / √5` |

---

## 11. 핵심 요약

1. **선형 동차 점화 관계**는 `aₙ = c₁aₙ₋₁ + ... + cₖaₙ₋ₖ` 형태이며, **특성 방정식**으로 일반항을 구한다.
2. 특성 방정식 `rᵏ - c₁rᵏ⁻¹ - ... - cₖ = 0`의 근이 `r₁, ..., rₖ`이면, 일반항은 `α₁r₁ⁿ + ... + αₖrₖⁿ`이다.
3. **비동차 점화 관계**의 해 = 특수해 + 연관 동차 관계의 일반해이다.
4. Lean 4에서 **꼬리 재귀**를 사용하면 O(n) 시간에 점화 관계를 계산할 수 있다.
5. `generalizing` 키워드는 귀납 가정을 더 강하게 만들어준다.
6. **비네 공식**은 피보나치 수열의 명시적 닫힌 형태이며, Lean 4에서 형식적으로 증명할 수 있다.

---

> **다음 파트 예고**: Part 11-C에서는 **분할정복 알고리즘과 점화 관계** (Section 8.3)를 다룬다. 이진탐색, 합병정렬 등의 분할정복 알고리즘의 복잡도를 점화 관계로 분석하고, **마스터 정리**(Master Theorem)를 소개한다!
