# Lean4 완전 정복 가이드 — 제8-B편

## **수학적 귀납법**(Mathematical Induction) — 부등식, 나누어짐, 집합 증명과 오류 분석

> **교재**: Kenneth H. Rosen, "Discrete Mathematics and Its Applications" 8판, 5.1절 (예제 5~15)  
> **참고**: 『Mathematics in Lean』 Chapter 5.2, 5.4  
> **선수 학습**: 제8-A편 (귀납법 기본, 합의 공식)

---

## 8B.0 이 장의 목표

1. **부등식**(inequality)에 대한 귀납법 증명 — 예제 5, 6
2. **나누어짐**(divisibility)에 대한 귀납법 증명 — 예제 8, 9
3. 귀납법을 이용한 증명에서의 **오류**(error) 찾기 — 예제 15
4. **재귀 함수**(recursive function)와 귀납법의 관계
5. 종합 연습문제

---

## 8B.1 교재 예제 5: n < 2ⁿ

### 8B.1.1 문제

> **예제 5**: 모든 양의 정수 n에 대해 n < 2ⁿ을 증명하라.

### 8B.1.2 수학적 증명

**기본 단계** (n = 1): 1 < 2¹ = 2 ✓

**귀납적 단계**: k < 2ᵏ라 가정(IH). 보여야 할 것: k + 1 < 2ᵏ⁺¹.

```
k + 1 < 2ᵏ + 1     ← IH에 의해 (k < 2ᵏ이므로)
      ≤ 2ᵏ + 2ᵏ     ← 1 ≤ 2ᵏ (k ≥ 1)
      = 2 · 2ᵏ = 2ᵏ⁺¹
```

### 8B.1.3 Lean4 구현 — `calc` 전술 소개

**`calc`**(계산 체인)은 여러 부등식/등식을 **연결**하는 전술이다:

```lean
-- 교재 예제 5: n < 2^n
theorem n_lt_two_pow (n : ℕ) (hn : 1 ≤ n) : n < 2 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : n = 0
    · subst h; norm_num
    · have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h
      have ih' := ih hn'
      have pow_pos : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
      calc n + 1 < 2 ^ n + 1 := by omega       -- IH 활용
           _ ≤ 2 ^ n + 2 ^ n := by omega         -- 1 ≤ 2^n
           _ = 2 ^ (n + 1) := by ring            -- 정리
```

### 8B.1.4 `calc` 전술 상세 설명

`calc`에서 `_`는 **이전 줄의 우변**을 가리킨다:

```lean
calc a < b := by ...    -- a < b 증명
     _ ≤ c := by ...    -- b ≤ c (여기서 _ = b)
     _ = d := by ...    -- c = d (여기서 _ = c)
-- 결론: a < d (추이율에 의해)
```

`<`, `≤`, `=`를 자유롭게 섞을 수 있으며, Lean4가 자동으로 추이율을 적용한다.

### 8B.1.5 중간 괄호 채우기 연습

```lean
theorem n_lt_two_pow_practice (n : ℕ) (hn : 1 ≤ n) : n < 2 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : n = 0
    · subst h; norm_num
    · have hn' : 1 ≤ n := ___           -- 🔲
      have ih' := ih hn'
      have pow_pos : 1 ≤ 2 ^ n := ___   -- 🔲
      calc n + 1 < ___ := by omega       -- 🔲
           _ ≤ ___ := by omega            -- 🔲
           _ = 2 ^ (n + 1) := by ring
```

<details>
<summary>💡 답 보기</summary>

```lean
      have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h
      have pow_pos : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
      calc n + 1 < 2 ^ n + 1 := by omega
           _ ≤ 2 ^ n + 2 ^ n := by omega
           _ = 2 ^ (n + 1) := by ring
```

</details>

---

## 8B.2 교재 예제 6: 2ⁿ < n! (n ≥ 4)

### 8B.2.1 문제

> **예제 6**: n ≥ 4인 모든 양의 정수 n에 대해 2ⁿ < n!임을 증명하라.

### 8B.2.2 수학적 증명

**기본 단계** (n = 4): 2⁴ = 16 < 24 = 4! ✓

**귀납적 단계**: k ≥ 4이고 2ᵏ < k!라 가정.
```
2ᵏ⁺¹ = 2 · 2ᵏ < 2 · k! < (k+1) · k! = (k+1)!
```
(k ≥ 4이므로 k + 1 ≥ 5 > 2)

### 8B.2.3 Lean4 구현 — `nlinarith` 소개

**`nlinarith`**: **비선형**(nonlinear) 산술을 처리하는 전술. `linarith`(선형만)보다 강력하다.

```lean
-- 교재 예제 6: 2^n < n! (n ≥ 4)
theorem pow_lt_fac (n : ℕ) (hn : 4 ≤ n) : 2 ^ n < n.factorial := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [Nat.factorial_succ]
    by_cases h : n = 3
    · subst h; norm_num [Nat.factorial]
    · have hn' : 4 ≤ n := by omega
      have ih' := ih hn'
      calc 2 ^ (n + 1) = 2 * 2 ^ n := by ring
           _ < 2 * n.factorial := by linarith
           _ ≤ (n + 1) * n.factorial := by nlinarith
```

### 8B.2.4 sorry 연습

```lean
theorem pow_lt_fac_challenge (n : ℕ) (hn : 4 ≤ n) : 2 ^ n < n.factorial := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem pow_lt_fac_challenge (n : ℕ) (hn : 4 ≤ n) : 2 ^ n < n.factorial := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [Nat.factorial_succ]
    by_cases h : n = 3
    · subst h; norm_num [Nat.factorial]
    · have hn' : 4 ≤ n := by omega
      calc 2 ^ (n + 1) = 2 * 2 ^ n := by ring
           _ < 2 * n.factorial := by linarith [ih hn']
           _ ≤ (n + 1) * n.factorial := by nlinarith
```

</details>

---

## 8B.3 교재 예제 8: n³ − n은 3으로 나누어짐

### 8B.3.1 문제

> **예제 8**: n이 양의 정수일 때 n³ − n이 3으로 나누어짐을 증명하라.

### 8B.3.2 핵심 트릭

```
(k+1)³ − (k+1) = (k³ − k) + 3(k² + k)
```

첫째 항은 IH에 의해 3의 배수, 둘째 항은 3의 배수 → 합도 3의 배수!

### 8B.3.3 Lean4 구현

```lean
-- 교재 예제 8: 3 ∣ (n³ - n) — 정수 버전
theorem dvd_cube_sub (n : ℤ) : 3 ∣ (n ^ 3 - n) := by
  have : n ^ 3 - n = n * (n - 1) * (n + 1) := by ring
  rw [this]
  -- 연속 세 정수의 곱은 항상 6의 배수 (따라서 3의 배수)
  -- omega가 처리할 수 있다
  omega
```

귀납법으로 풀면:

```lean
-- 양의 자연수에 대해 귀납법으로:
-- n³ 과 n의 mod 3이 같음을 보임
theorem cube_mod_three (n : ℕ) : n ^ 3 % 3 = n % 3 := by
  omega
```

> 💡 `omega`가 한 줄에 해결하지만, 귀납법의 **구조**를 이해하는 것이 중요하다!

### 8B.3.4 귀납법 구조로 상세하게

```lean
-- 귀납법 구조를 명시적으로 보여주는 증명
theorem three_dvd_cube_sub_explicit (n : ℕ) : 3 ∣ ((n + 1) ^ 3 - (n + 1) : ℤ) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    -- 핵심: (n+2)³ - (n+2) = ((n+1)³ - (n+1)) + 3((n+1)² + (n+1))
    have key : ((↑n + 2 : ℤ)) ^ 3 - (↑n + 2) =
               ((↑n + 1) ^ 3 - (↑n + 1)) + 3 * ((↑n + 1) ^ 2 + (↑n + 1)) := by ring
    rw [key]
    exact dvd_add ih (dvd_mul_right 3 _)
```

### 8B.3.5 중간 괄호 채우기

```lean
theorem three_dvd_practice (n : ℕ) : 3 ∣ ((n + 1) ^ 3 - (n + 1) : ℤ) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have key : ((↑n + 2 : ℤ)) ^ 3 - (↑n + 2) =
               ((↑n + 1) ^ 3 - (↑n + 1)) + 3 * ((↑n + 1) ^ 2 + (↑n + 1)) := by ___
    rw [___]
    exact dvd_add ___ (dvd_mul_right 3 _)
```

<details>
<summary>💡 답 보기</summary>

```lean
    have key : ... := by ring
    rw [key]
    exact dvd_add ih (dvd_mul_right 3 _)
```

</details>

---

## 8B.4 교재 예제 9: 7ⁿ⁺² + 8²ⁿ⁺¹은 57로 나누어짐

### 8B.4.1 문제

> **예제 9**: 모든 음이 아닌 정수 n에 대하여 7ⁿ⁺² + 8²ⁿ⁺¹은 57로 나누어짐을 증명하라.

### 8B.4.2 핵심 트릭

```
7^(k+3) + 8^(2k+3) = 7 · (7^(k+2) + 8^(2k+1)) + 57 · 8^(2k+1)
```

= 7 × (IH 부분) + 57 × (명백한 배수)

### 8B.4.3 Lean4 구현

```lean
theorem dvd_57 (n : ℕ) : 57 ∣ (7 ^ (n + 2) + 8 ^ (2 * n + 1)) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have key : 7 ^ (n + 3) + 8 ^ (2 * n + 3)
             = 7 * (7 ^ (n + 2) + 8 ^ (2 * n + 1)) + 57 * 8 ^ (2 * n + 1) := by ring
    rw [key]
    exact dvd_add (dvd_mul_of_dvd_right ih 7) (dvd_mul_right 57 _)
```

### 8B.4.4 sorry 연습

```lean
theorem dvd_57_challenge (n : ℕ) : 57 ∣ (7 ^ (n + 2) + 8 ^ (2 * n + 1)) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem dvd_57_challenge (n : ℕ) : 57 ∣ (7 ^ (n + 2) + 8 ^ (2 * n + 1)) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have key : 7 ^ (n + 3) + 8 ^ (2 * n + 3)
             = 7 * (7 ^ (n + 2) + 8 ^ (2 * n + 1)) + 57 * 8 ^ (2 * n + 1) := by ring
    rw [key]
    exact dvd_add (dvd_mul_of_dvd_right ih 7) (dvd_mul_right 57 _)
```

</details>

---

## 8B.5 교재 예제 15: 귀납법의 **오류** 찾기

### 8B.5.1 문제

> '평면에서 어떤 두 직선도 평행하지 않은 직선들의 모든 집합은 같은 점에서 만난다'라는 명백히 틀린 주장의 "증명"에서 오류를 찾아라.

### 8B.5.2 "증명"의 구조

- P(n): "서로 평행하지 않은 n개의 직선은 한 점에서 만난다"
- 기본 단계: P(2) ✓ (평행하지 않은 두 직선은 한 점에서 만남)
- 귀납적 단계: P(k) 가정하에 P(k+1) 증명

### 8B.5.3 오류의 위치

**k = 2에서 P(2) → P(3)이 작동하지 않는다!**

3개의 직선 l₁, l₂, l₃이 있을 때:
- {l₁, l₂}는 한 점 p₁에서 만남 (P(2))
- {l₂, l₃}는 한 점 p₂에서 만남 (P(2))
- **문제**: p₁ = p₂를 보여야 하는데, 두 집합이 **공유하는** 직선이 l₂ 하나뿐이라 p₁ = p₂를 강제할 수 없다!

> **교훈**: 귀납적 단계가 **모든 k에서** 작동하는지, 특히 **작은 k에서** 반드시 검증하라!

### 8B.5.4 Lean4에서의 교훈

Lean4 같은 형식 검증 시스템을 사용하면 이런 오류를 **자동으로 잡는다**. 증명의 모든 단계가 논리적으로 유효한지 기계적으로 검증하기 때문이다.

---

## 8B.6 **재귀 함수**와 귀납법 — Mathematics in Lean

### 8B.6.1 재귀 정의와 귀납 증명의 대응

| | 재귀 함수 | 귀납법 증명 |
|---|---------|-----------|
| 기본 | `\| 0 => ...` | `\| zero => ...` |
| 재귀 | `\| n+1 => ... f n ...` | `\| succ n ih => ... ih ...` |

```lean
-- 팩토리얼 (재귀 정의)
def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

-- 팩토리얼은 항상 양수 (귀납 증명)
theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction n with
  | zero => rw [fac]; exact zero_lt_one
  | succ n ih => rw [fac]; exact mul_pos n.succ_pos ih
```

### 8B.6.2 피보나치 수열

```lean
@[simp] def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

-- 연속 피보나치 수는 서로소
theorem fib_coprime (n : ℕ) : Nat.Coprime (fib n) (fib (n + 1)) := by
  induction n with
  | zero => simp [fib]
  | succ n ih =>
    simp only [fib, Nat.coprime_add_self_right]
    exact ih.symm
```

---

## 8B.7 연습 세트

### 연습 8B.1: 홀수 제곱의 합

```lean
-- 3 * ∑(2i+1)² = (n+1)(2n+1)(2n+3)
theorem sum_odd_sq (n : ℕ) :
    3 * (∑ i ∈ Finset.range (n + 1), (2 * i + 1) ^ 2) =
    (n + 1) * (2 * n + 1) * (2 * n + 3) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, mul_add, ih]; ring
```

</details>

### 연습 8B.2: n² + n은 2의 배수

```lean
theorem even_sq_add (n : ℕ) : 2 ∣ (n ^ 2 + n) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
  have : n ^ 2 + n = n * (n + 1) := by ring
  rw [this]; omega
```

</details>

### 연습 8B.3: n³ + 2n은 3의 배수

```lean
theorem three_dvd_cube_plus (n : ℤ) : 3 ∣ (n ^ 3 + 2 * n) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
  have : n ^ 3 + 2 * n = n ^ 3 - n + 3 * n := by ring
  rw [this]; exact dvd_add (by omega) (dvd_mul_right 3 _)
```

</details>

### 연습 8B.4 (도전): 베르누이 부등식 (자연수 특수 경우)

```lean
-- 1 + n * h ≤ (1 + h)^n
theorem bernoulli_nat (n h : ℕ) : 1 + n * h ≤ (1 + h) ^ n := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
  induction n with
  | zero => simp
  | succ n ih =>
    calc 1 + (n + 1) * h = (1 + n * h) + h := by ring
      _ ≤ (1 + h) ^ n + h := by linarith
      _ ≤ (1 + h) ^ n * (1 + h) := by nlinarith [Nat.one_le_pow n (1+h) (by omega)]
      _ = (1 + h) ^ (n + 1) := by rw [pow_succ]
```

</details>

### 연습 8B.5 (도전): fac(n) > 0 직접 증명

```lean
def my_fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * my_fac n

theorem my_fac_pos (n : ℕ) : 0 < my_fac n := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
  induction n with
  | zero => rw [my_fac]; exact zero_lt_one
  | succ n ih => rw [my_fac]; exact mul_pos n.succ_pos ih
```

</details>

---

## 8B.8 전술 요약

| 전술/개념 | 용도 | 예시 |
|---------|------|------|
| `calc` | 계산 체인 | `calc a < b ... _ ≤ c ...` |
| `nlinarith` | 비선형 산술 | 곱셈 포함 부등식 |
| `by_cases` | 경우 분리 | `by_cases h : n = 0` |
| `subst` | 등식 가설로 변수 치환 | `h : n = 3 → subst h` |
| `dvd_add` | 나눗셈의 합 보존 | `a∣b → a∣c → a∣(b+c)` |
| `dvd_mul_of_dvd_right` | 배수 곱 보존 | `a∣b → a∣(c*b)` |
| `Nat.factorial_succ` | `(n+1)! = (n+1)*n!` | 팩토리얼 분해 |
| `pow_succ` | `a^(n+1) = a^n * a` | 거듭제곱 분해 |

---

## 다음 편(8-C) 예고

**제8-C편**에서는 교재 5.2절의 내용을 다룬다:
- **강 귀납법**(strong induction) — P(1)∧...∧P(k) → P(k+1)
- **순서화 성질**(well-ordering property)과 귀납법의 동치
- Lean4의 `Nat.strong_rec_on`
- 우표 문제, 소인수 존재 정리

---

**(끝)**
