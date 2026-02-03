# Lean4 완전 정복 가이드 — 제5편 (Part A)

## 기초: 계산과 대수적 구조

> **교재**: Mathematics in Lean, Chapter 2 "Basics"  
> **범위**: 2.1절 Calculating, 2.2절 Proving Identities in Algebraic Structures  
> **선수 학습**: 제4편(명제 논리, 술어 논리, 증명 방법)

---

## 5.0 이 장의 목표

이 장에서는 다음을 학습한다:

1. **재작성**(Rewriting)과 `rw` 전술의 원리
2. **계산 증명**(calc)을 이용한 단계별 증명
3. **환**(Ring)과 **가환환**(Commutative Ring)의 공리
4. **ring** 전술을 이용한 자동 증명
5. **군**(Group)의 기본 정리 증명
6. `have` 전술로 **보조 정리** 도입하기

---

## 5.1 재작성(Rewriting)의 기초

### 5.1.1 재작성이란?

**재작성**(rewriting)은 **등식을 이용하여 목표를 변환**하는 증명 기법이다.

예를 들어, `a * b = b * a`(곱셈의 교환법칙)가 주어지면:
- 목표에서 `a * b`를 `b * a`로 **치환**할 수 있다

### 5.1.2 `rw` 전술의 기본 사용법

```lean
-- rw [정리] : 정리의 좌변을 우변으로 치환
-- rw [← 정리] : 정리의 우변을 좌변으로 치환 (역방향)

-- 예제: a * b * c = b * (a * c) 증명
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]      -- a * b를 b * a로 치환 → b * a * c = b * (a * c)
  rw [mul_assoc b a c]   -- b * a * c를 b * (a * c)로 치환 → 완료!
```

### 5.1.3 `rw`의 동작 원리

`rw [h]`에서 `h : A = B`이면:
1. 현재 목표에서 `A`와 일치하는 부분을 찾는다
2. 그 부분을 `B`로 **치환**한다
3. 새로운 목표가 된다

```lean
-- 단계별 상태 확인
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  -- 현재 목표: a * b * c = b * (a * c)
  rw [mul_comm a b]
  -- mul_comm a b : a * b = b * a
  -- a * b를 b * a로 치환
  -- 새 목표: b * a * c = b * (a * c)
  rw [mul_assoc b a c]
  -- mul_assoc b a c : b * a * c = b * (a * c)
  -- 새 목표: b * (a * c) = b * (a * c)
  -- 양변이 같으므로 자동 완료!
```

### 5.1.4 역방향 재작성: `←` 사용

`rw [← h]`에서 `h : A = B`이면:
- `B`를 `A`로 치환한다 (역방향)

```lean
-- ← 는 \l 또는 \leftarrow로 입력

example (a b c : ℝ) : a * (b * c) = a * b * c := by
  rw [← mul_assoc a b c]
  -- mul_assoc a b c : a * b * c = a * (b * c)
  -- 역방향: a * (b * c)를 a * b * c로 치환
  -- 목표가 a * b * c = a * b * c가 되어 완료!
```

### 5.1.5 핵심 등식 정리들

Lean4/Mathlib에서 제공하는 기본 등식 정리들:

| 정리 이름 | 내용 | 설명 |
|----------|------|------|
| `mul_assoc a b c` | `a * b * c = a * (b * c)` | 곱셈의 **결합법칙**(Associativity) |
| `mul_comm a b` | `a * b = b * a` | 곱셈의 **교환법칙**(Commutativity) |
| `add_assoc a b c` | `a + b + c = a + (b + c)` | 덧셈의 **결합법칙** |
| `add_comm a b` | `a + b = b + a` | 덧셈의 **교환법칙** |
| `mul_one a` | `a * 1 = a` | 곱셈의 **항등원**(Identity) |
| `one_mul a` | `1 * a = a` | 곱셈의 항등원 (좌) |
| `add_zero a` | `a + 0 = a` | 덧셈의 항등원 |
| `zero_add a` | `0 + a = a` | 덧셈의 항등원 (좌) |

### 5.1.6 인자 생략

정리에 인자를 생략하면 Lean이 **자동으로 매칭**한다:

```lean
-- 인자를 모두 제공
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc a b c]    -- a * b * c → a * (b * c)
  rw [mul_comm a (b * c)] -- a * (b * c) → (b * c) * a
  rw [mul_assoc b c a]    -- (b * c) * a → b * (c * a)  -- 오류 가능!

-- 인자를 생략하면 Lean이 패턴 매칭
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]   -- 첫 번째 매칭되는 패턴에 적용
  rw [mul_comm]    -- 자동 매칭
```

### 5.1.7 부분 인자 제공

일부 인자만 제공하여 **특정 위치를 지정**할 수 있다:

```lean
-- mul_comm a는 "a * ?"에 매칭
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm a]    -- a * (b * c) → (b * c) * a
  rw [mul_assoc]     -- (b * c) * a → b * (c * a)
```

---

### 5.1.8 연습문제 1: 기본 재작성

#### 연습 1-1: 두 번의 재작성
```lean
-- c * b * a = b * (a * c)를 증명하라
-- 힌트: mul_comm, mul_assoc 사용

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]      -- c * b * a → b * c * a
  rw [mul_assoc b c a]   -- b * c * a → b * (c * a)
  rw [mul_comm c a]      -- b * (c * a) → b * (a * c)
```

**단계별 설명**:
1. `mul_comm c b`: c * b를 b * c로
2. `mul_assoc b c a`: b * c * a를 b * (c * a)로
3. `mul_comm c a`: c * a를 a * c로

</details>

#### 연습 1-2: 역방향 재작성
```lean
-- a * (b * c) = b * (a * c)를 증명하라

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc a b c]  -- a * (b * c) → a * b * c
  rw [mul_comm a b]       -- a * b * c → b * a * c
  rw [mul_assoc b a c]    -- b * a * c → b * (a * c)
```

</details>

#### 연습 1-3: 덧셈 재작성
```lean
-- a + b + c = c + b + a를 증명하라

example (a b c : ℝ) : a + b + c = c + b + a := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (a b c : ℝ) : a + b + c = c + b + a := by
  rw [add_comm a b]      -- a + b + c → b + a + c
  rw [add_assoc b a c]   -- b + a + c → b + (a + c)
  rw [add_comm a c]      -- b + (a + c) → b + (c + a)
  rw [← add_assoc b c a] -- b + (c + a) → b + c + a
  rw [add_comm b c]      -- b + c + a → c + b + a
```

**또는 더 간단히**:
```lean
example (a b c : ℝ) : a + b + c = c + b + a := by
  ring  -- 자동으로 해결!
```

</details>

#### 연습 1-4: 인자 생략 연습
```lean
-- a * b * c = b * c * a를 인자 생략으로 증명하라

example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]  -- 힌트: 첫 번째 단계
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]   -- a * b * c → a * (b * c)
  rw [mul_comm]    -- a * (b * c) → (b * c) * a
  rw [mul_assoc]   -- (b * c) * a → b * (c * a)  
  rw [mul_comm c a] -- b * (c * a) → b * (a * c) -- 이건 목표가 아님!
  -- 다시:
```

더 정확한 풀이:
```lean
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_comm a b]    -- a * b * c → b * a * c
  rw [mul_assoc]       -- b * a * c → b * (a * c)
  rw [mul_comm a c]    -- b * (a * c) → b * (c * a)
  rw [← mul_assoc]     -- b * (c * a) → b * c * a
```

</details>

---

## 5.2 가설에서의 재작성

### 5.2.1 `rw ... at` 문법

가설(hypothesis)에서 재작성하려면 `at` 키워드를 사용한다:

```lean
-- rw [정리] at 가설이름

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : 
    a * (b * e) = c * (d * f) := by
  rw [h'] at h     -- 아니, h'를 목표나 다른 곳에 적용
  -- h' : e = f를 이용해 목표의 e를 f로 바꾸려면:
  rw [h']          -- 목표에서 e를 f로: a * (b * f) = c * (d * f)
  rw [← mul_assoc] -- a * (b * f) → a * b * f
  rw [h]           -- a * b * f → c * d * f (h 사용)
  rw [mul_assoc]   -- c * d * f → c * (d * f)
```

### 5.2.2 상세 예제

```lean
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : 
    c = 2 * a * d := by
  rw [hyp'] at hyp      -- hyp의 b를 a * d로 치환
  -- hyp : c = d * a + a * d
  rw [mul_comm d a] at hyp  -- hyp의 d * a를 a * d로
  -- hyp : c = a * d + a * d
  rw [← two_mul (a * d)] at hyp  -- a * d + a * d를 2 * (a * d)로
  -- hyp : c = 2 * (a * d)
  rw [← mul_assoc 2 a d] at hyp  -- 2 * (a * d)를 2 * a * d로
  -- hyp : c = 2 * a * d
  exact hyp
```

### 5.2.3 `exact` 전술

`exact` 전술은 **목표와 정확히 일치하는 증명을 제공**한다:

```lean
-- exact h : h가 현재 목표와 정확히 일치할 때 사용

example (P : Prop) (h : P) : P := by
  exact h

example (a b : ℝ) (h : a = b) : a = b := by
  exact h
```

---

### 5.2.4 연습문제 2: 가설에서 재작성

#### 연습 2-1: 가설 변환 후 적용
```lean
example (a b c d e f : ℝ) (h : b * c = e * f) : 
    a * b * c * d = a * e * f * d := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (a b c d e f : ℝ) (h : b * c = e * f) : 
    a * b * c * d = a * e * f * d := by
  rw [mul_assoc a b c]     -- a * b * c * d → a * (b * c) * d
  rw [h]                    -- a * (b * c) * d → a * (e * f) * d
  rw [← mul_assoc a e f]   -- a * (e * f) * d → a * e * f * d
```

</details>

#### 연습 2-2: sub_self 정리 사용
```lean
-- sub_self a : a - a = 0

example (a b c : ℝ) (h : a = b) : a - b = 0 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (a b c : ℝ) (h : a = b) : a - b = 0 := by
  rw [h]          -- a - b → b - b
  rw [sub_self]   -- b - b → 0
```

</details>

---

## 5.3 calc 블록: 계산 증명

### 5.3.1 calc이란?

`calc`(calculation)는 **단계별 계산 증명**을 작성하는 구문이다.

수학에서 흔히 보는 형태:
```
A = B    (이유1)
  = C    (이유2)
  = D    (이유3)
```

이것을 Lean4에서:
```lean
calc A = B := by 이유1
     _ = C := by 이유2
     _ = D := by 이유3
```

### 5.3.2 calc 기본 예제

```lean
-- (a + b) * (a + b) = a * a + 2 * (a * b) + b * b
-- 즉, (a + b)² = a² + 2ab + b²

example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) 
        = a * a + b * a + (a * b + b * b) := by
          rw [mul_add, add_mul, add_mul]
      _ = a * a + (b * a + a * b) + b * b := by
          rw [← add_assoc, add_assoc (a * a)]
      _ = a * a + 2 * (a * b) + b * b := by
          rw [mul_comm b a, ← two_mul]
```

### 5.3.3 calc 구문 규칙

1. 첫 줄: `calc 시작식 = 다음식 := by 증명`
2. 이후 줄: `_ = 다음식 := by 증명` (밑줄 `_`은 이전 결과)
3. **들여쓰기가 중요**! 일관되게 유지해야 함
4. `=` 대신 `≤`, `<` 등 다른 관계도 사용 가능

### 5.3.4 calc에서 sorry 사용

복잡한 증명을 작성할 때, 먼저 구조를 잡고 나중에 각 단계를 채울 수 있다:

```lean
example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) 
        = a * a + b * a + (a * b + b * b) := by sorry
      _ = a * a + (b * a + a * b) + b * b := by sorry
      _ = a * a + 2 * (a * b) + b * b := by sorry
```

---

### 5.3.5 연습문제 3: calc 증명

#### 연습 3-1: 전개 공식
```lean
-- (a + b) * (c + d) = a * c + a * d + b * c + b * d를 calc로 증명
-- 힌트: mul_add, add_mul 사용

example (a b c d : ℝ) : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
  calc
    (a + b) * (c + d) = sorry := by sorry
      _ = sorry := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (a b c d : ℝ) : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
  calc
    (a + b) * (c + d) 
        = a * (c + d) + b * (c + d) := by rw [add_mul]
      _ = a * c + a * d + (b * c + b * d) := by rw [mul_add, mul_add]
      _ = a * c + a * d + b * c + b * d := by rw [← add_assoc]
```

</details>

#### 연습 3-2: 곱셈 공식
```lean
-- (a + b) * (a - b) = a² - b²를 calc로 증명
-- 힌트: pow_two a : a ^ 2 = a * a
--       mul_sub, add_mul, sub_sub, add_sub 등

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 :=
  calc
    (a + b) * (a - b) = sorry := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring
```

또는 calc로:
```lean
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 :=
  calc
    (a + b) * (a - b) 
        = a * (a - b) + b * (a - b) := by rw [add_mul]
      _ = a * a - a * b + (b * a - b * b) := by rw [mul_sub, mul_sub]
      _ = a * a - a * b + b * a - b * b := by ring
      _ = a * a - b * b := by ring
      _ = a ^ 2 - b ^ 2 := by rw [← pow_two, ← pow_two]
```

</details>

---

## 5.4 ring 전술

### 5.4.1 ring이란?

`ring` 전술은 **환(Ring)의 공리만으로 증명 가능한 등식**을 자동으로 증명한다.

```lean
-- ring 전술 예제
example (a b c : ℝ) : c * b * a = b * (a * c) := by ring
example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring
```

### 5.4.2 ring의 한계

`ring`은 **순수하게 환 공리에서 따라오는 등식**만 증명한다:
- 지역 가설(local hypothesis)은 사용하지 **않는다**
- 부등식은 증명하지 **않는다**

```lean
-- 이것은 안 된다:
example (a b : ℝ) (h : a = b) : a + 1 = b + 1 := by
  ring  -- 실패! ring은 h를 사용하지 않음

-- 대신:
example (a b : ℝ) (h : a = b) : a + 1 = b + 1 := by
  rw [h]  -- h를 사용해 a를 b로 치환
```

### 5.4.3 rw와 ring의 조합

가설을 먼저 적용한 후 ring을 사용:

```lean
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : 
    c = 2 * a * d := by
  rw [hyp, hyp']  -- c를 전개
  ring            -- 나머지는 ring이 처리
```

---

### 5.4.4 연습문제 4: ring 사용

#### 연습 4-1: 단순 등식
```lean
example (a b c : ℝ) : a * (b + c) = a * b + a * c := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (a b c : ℝ) : a * (b + c) = a * b + a * c := by
  ring
```

</details>

#### 연습 4-2: 복잡한 등식
```lean
example (a b : ℝ) : (a + b) ^ 3 = a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (a b : ℝ) : (a + b) ^ 3 = a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 := by
  ring
```

</details>

#### 연습 4-3: 가설과 ring 조합
```lean
example (a b c : ℝ) (h : a = 2 * b) : a * c = 2 * b * c := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (a b c : ℝ) (h : a = 2 * b) : a * c = 2 * b * c := by
  rw [h]
  -- 또는 그냥:
  -- rw [h]; ring
```

</details>

---

## 5.5 환(Ring)의 공리

### 5.5.1 환이란?

수학적으로 **환**(Ring)은 집합 R과 연산 +, ×, 상수 0, 1, 그리고 음수 연산 -로 구성되며 다음을 만족한다:

| 공리 | Lean4 이름 | 내용 |
|-----|-----------|------|
| 덧셈 결합법칙 | `add_assoc` | `a + b + c = a + (b + c)` |
| 덧셈 교환법칙 | `add_comm` | `a + b = b + a` |
| 덧셈 항등원 (0) | `zero_add` | `0 + a = a` |
| 덧셈 역원 | `neg_add_cancel` | `-a + a = 0` |
| 곱셈 결합법칙 | `mul_assoc` | `a * b * c = a * (b * c)` |
| 곱셈 항등원 (1) | `mul_one`, `one_mul` | `a * 1 = a`, `1 * a = a` |
| 분배법칙 (좌) | `mul_add` | `a * (b + c) = a * b + a * c` |
| 분배법칙 (우) | `add_mul` | `(a + b) * c = a * c + b * c` |

### 5.5.2 Lean4에서 환 선언

```lean
-- 타입 R이 환의 구조를 가짐을 선언
variable (R : Type*) [Ring R]

-- 이제 R의 원소에 대해 환 공리를 사용할 수 있다
#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)
```

### 5.5.3 가환환(CommRing)

**가환환**(Commutative Ring)은 곱셈의 교환법칙도 만족하는 환이다:

```lean
variable (R : Type*) [CommRing R]

#check (mul_comm : ∀ a b : R, a * b = b * a)

-- 실수(ℝ), 유리수(ℚ), 복소수(ℂ)는 모두 가환환
-- 행렬은 일반적으로 가환환이 아님!
```

---

## 5.6 환의 기본 정리 증명

### 5.6.1 add_zero 유도

`add_zero`(a + 0 = a)는 공리가 아니라 다른 공리에서 **유도**된다:

```lean
-- zero_add : 0 + a = a (공리)
-- add_comm : a + b = b + a (공리)

theorem my_add_zero (R : Type*) [Ring R] (a : R) : a + 0 = a := by
  rw [add_comm]   -- a + 0 → 0 + a
  rw [zero_add]   -- 0 + a → a
```

### 5.6.2 add_neg_cancel 유도

```lean
-- neg_add_cancel : -a + a = 0 (공리)

theorem my_add_neg_cancel (R : Type*) [Ring R] (a : R) : a + -a = 0 := by
  rw [add_comm]       -- a + -a → -a + a
  rw [neg_add_cancel] -- -a + a → 0
```

### 5.6.3 neg_add_cancel_left

```lean
-- 유용한 보조정리: -a + (a + b) = b

theorem neg_add_cancel_left (R : Type*) [Ring R] (a b : R) : 
    -a + (a + b) = b := by
  rw [← add_assoc]    -- -a + (a + b) → -a + a + b
  rw [neg_add_cancel] -- -a + a + b → 0 + b
  rw [zero_add]       -- 0 + b → b
```

---

### 5.6.4 연습문제 5: 환 정리 증명

#### 연습 5-1: add_neg_cancel_right
```lean
-- a + b + -b = a를 증명하라

theorem add_neg_cancel_right (R : Type*) [Ring R] (a b : R) : 
    a + b + -b = a := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem add_neg_cancel_right (R : Type*) [Ring R] (a b : R) : 
    a + b + -b = a := by
  rw [add_assoc]       -- a + b + -b → a + (b + -b)
  rw [add_neg_cancel]  -- a + (b + -b) → a + 0  (위에서 증명한 것 또는 공리에서)
  rw [add_zero]        -- a + 0 → a
```

**참고**: `add_neg_cancel`이 `b + -b = 0`인지 확인 필요. 일부 버전에서는 `add_neg_self`.

</details>

#### 연습 5-2: add_left_cancel
```lean
-- a + b = a + c이면 b = c

theorem add_left_cancel (R : Type*) [Ring R] {a b c : R} (h : a + b = a + c) : 
    b = c := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem add_left_cancel (R : Type*) [Ring R] {a b c : R} (h : a + b = a + c) : 
    b = c := by
  -- -a를 양변에 더한다
  have h1 : -a + (a + b) = -a + (a + c) := by rw [h]
  -- 좌변 정리: -a + (a + b) = b
  rw [neg_add_cancel_left] at h1
  -- 우변 정리: -a + (a + c) = c
  rw [neg_add_cancel_left] at h1
  exact h1
```

또는 더 간단히:
```lean
theorem add_left_cancel' (R : Type*) [Ring R] {a b c : R} (h : a + b = a + c) : 
    b = c := by
  calc b = -a + (a + b) := by rw [neg_add_cancel_left]
       _ = -a + (a + c) := by rw [h]
       _ = c := by rw [neg_add_cancel_left]
```

</details>

#### 연습 5-3: add_right_cancel
```lean
-- a + b = c + b이면 a = c

theorem add_right_cancel (R : Type*) [Ring R] {a b c : R} (h : a + b = c + b) : 
    a = c := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem add_right_cancel (R : Type*) [Ring R] {a b c : R} (h : a + b = c + b) : 
    a = c := by
  have h1 : a + b + -b = c + b + -b := by rw [h]
  rw [add_neg_cancel_right] at h1
  rw [add_neg_cancel_right] at h1
  exact h1
```

</details>

---

## 5.7 have 전술: 보조 정리 도입

### 5.7.1 have란?

`have` 전술은 **증명 중에 보조 사실을 도입**한다:

```lean
have 이름 : 명제 := by 증명
-- 이후 '이름'을 가설로 사용할 수 있음
```

### 5.7.2 have 예제: mul_zero 증명

`a * 0 = 0`을 환 공리만으로 증명:

```lean
theorem mul_zero (R : Type*) [Ring R] (a : R) : a * 0 = 0 := by
  -- 핵심 아이디어: a * 0 + a * 0 = a * 0 + 0을 보이고
  -- add_left_cancel을 적용
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    -- 좌변: a * 0 + a * 0 = a * (0 + 0) = a * 0
    -- 우변: a * 0 + 0 = a * 0
    rw [← mul_add]  -- a * 0 + a * 0 → a * (0 + 0)
    rw [add_zero]   -- a * (0 + 0) → a * 0
    rw [add_zero]   -- a * 0 + 0 → a * 0 (우변도 정리)
  -- h : a * 0 + a * 0 = a * 0 + 0
  -- add_left_cancel 적용: a * 0 = 0
  exact add_left_cancel h
```

### 5.7.3 have의 들여쓰기

`have` 다음에 들여쓰기된 블록은 그 보조 사실의 증명이다:

```lean
theorem example_have (P Q R : Prop) (hp : P) (hpq : P → Q) (hqr : Q → R) : R := by
  have hq : Q := by    -- Q를 증명할 것임
    exact hpq hp       -- 들여쓰기된 증명
  have hr : R := by    -- R을 증명할 것임
    exact hqr hq       -- hq 사용 가능
  exact hr
```

---

### 5.7.4 연습문제 6: have 사용

#### 연습 6-1: zero_mul
```lean
-- 0 * a = 0을 증명하라 (곱셈이 교환적이지 않을 수 있음!)

theorem zero_mul (R : Type*) [Ring R] (a : R) : 0 * a = 0 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem zero_mul (R : Type*) [Ring R] (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 * a + 0 := by
    rw [← add_mul]   -- 0 * a + 0 * a → (0 + 0) * a
    rw [add_zero]    -- (0 + 0) * a → 0 * a
    rw [add_zero]    -- 0 * a + 0 → 0 * a
  exact add_left_cancel h
```

</details>

#### 연습 6-2: neg_eq_of_add_eq_zero
```lean
-- a + b = 0이면 -a = b

theorem neg_eq_of_add_eq_zero (R : Type*) [Ring R] {a b : R} (h : a + b = 0) : 
    -a = b := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem neg_eq_of_add_eq_zero (R : Type*) [Ring R] {a b : R} (h : a + b = 0) : 
    -a = b := by
  -- -a = -a + 0 = -a + (a + b) = (-a + a) + b = 0 + b = b
  calc -a = -a + 0 := by rw [add_zero]
        _ = -a + (a + b) := by rw [h]
        _ = (-a + a) + b := by rw [add_assoc]
        _ = 0 + b := by rw [neg_add_cancel]
        _ = b := by rw [zero_add]
```

</details>

#### 연습 6-3: neg_neg
```lean
-- --a = a (이중 부정)

theorem neg_neg (R : Type*) [Ring R] (a : R) : - -a = a := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem neg_neg (R : Type*) [Ring R] (a : R) : - -a = a := by
  -- -a + a = 0이므로, neg_eq_of_add_eq_zero에 의해 -(-a) = a
  apply neg_eq_of_add_eq_zero
  rw [neg_add_cancel]
```

또는:
```lean
theorem neg_neg' (R : Type*) [Ring R] (a : R) : - -a = a := by
  have h : -a + a = 0 := neg_add_cancel a
  exact neg_eq_of_add_eq_zero h
```

</details>

---

## 5.8 nth_rw: 특정 위치 재작성

### 5.8.1 nth_rw란?

`nth_rw`는 목표에서 **n번째로 나타나는 패턴만** 재작성한다:

```lean
-- nth_rw n [정리] : n번째 매칭만 재작성 (1부터 시작)

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]    -- 두 번째 (a + b)만 c로 치환
  -- 목표: (a + b) * c = a * c + b * c
  rw [add_mul]    -- 분배법칙 적용
```

### 5.8.2 nth_rw 예제

```lean
example (a b : ℕ) : (a + b) + (a + b) = 2 * (a + b) := by
  nth_rw 1 [← one_mul (a + b)]  -- 첫 번째 (a + b)를 1 * (a + b)로
  -- 목표: 1 * (a + b) + (a + b) = 2 * (a + b)
  nth_rw 2 [← one_mul (a + b)]  -- 두 번째 (a + b)를 1 * (a + b)로
  -- 목표: 1 * (a + b) + 1 * (a + b) = 2 * (a + b)
  rw [← add_mul]                 -- 분배법칙 역적용
  -- 목표: (1 + 1) * (a + b) = 2 * (a + b)
  norm_num                       -- 1 + 1 = 2
```

---

**(Part B에서 계속: 정리와 보조정리 사용, 부등식 증명, apply와 exact, linarith)**
