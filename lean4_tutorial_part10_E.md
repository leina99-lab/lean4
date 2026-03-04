# Lean4 완전 정복 가이드 —  Part 10-E: 분산과 체비쇼프 부등식

> **Rosen 이산수학 8판 §7.4 기반 · Mathematics in Lean 참조**
> Part 10-D에서 **기댓값**(expected value)을 배웠다. 이제 확률변수가 기댓값으로부터 얼마나 **퍼져 있는지**를 측정하는 **분산**(variance)을 배운다.

---

##  이 파트에서 배울 것

1. **분산**(variance)과 **표준편차**(standard deviation)의 정의
2. 분산의 계산 공식: `V(X) = E(X²) - E(X)²`
3. 베르누이 시행에서의 분산
4. **비에나메의 공식**(Bienaymé's formula): 독립 확률변수 합의 분산
5. **체비쇼프 부등식**(Chebyshev's inequality): 확률의 상계
6. Lean 4에서의 형식화

---

## 10E.1 왜 분산이 필요한가?

###  동기 부여

두 확률변수 `X`와 `Y`가 같은 기댓값을 가진다고 해서 같은 "행동"을 하는 것은 아니다!

| | X (항상 0) | Y (-1 또는 1, 각 1/2) |
|---|---|---|
| 기댓값 | E(X) = 0 | E(Y) = 0 |
| 행동 | 항상 0 | 크게 변동 |

기댓값은 "중심"만 알려주고, 값들이 얼마나 **퍼져 있는지**는 알려주지 않는다. 이 "퍼짐 정도"를 측정하는 것이 **분산**이다.

---

## 10E.2 분산의 정의

###  정의 4

> `X`가 **표본공간**(sample space) `S`에서 정의된 확률변수라 하자. `X`의 **분산**(variance) `V(X)`는 다음과 같다:
>
> ```
> V(X) = Σ (X(s) - E(X))² · p(s)
>        s∈S
> ```
>
> 즉, `V(X)`는 `X`의 **편차**(deviation)의 **제곱**에 대한 **가중치 평균**이다.
>
> `X`의 **표준편차**(standard deviation) `σ(X)`는 `σ(X) = √V(X)` 로 정의된다.

### 🧠 직관적 이해

- **편차**(deviation): `X(s) - E(X)` = 각 결과값과 평균의 차이
- **편차의 제곱**: 양수/음수에 관계없이 거리를 측정
- **분산**: 편차 제곱의 가중 평균 → 평균으로부터의 "평균적 거리²"
- **표준편차**: 분산의 제곱근 → 원래 단위로 돌아옴

### Lean 4로 표현

```lean
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

open Finset

/-- 분산: V(X) = Σ (X(s) - E(X))² · p(s) -/
def variance (n : ℕ) (p X : Fin n → ℚ) : ℚ :=
  let mean := ∑ s : Fin n, p s * X s
  ∑ s : Fin n, (X s - mean)^2 * p s
```

---

## 10E.3 정리 6: 분산의 계산 공식 

직접 정의대로 분산을 구하는 것은 번거롭다. 다음 공식이 훨씬 편리하다!

###  정리 6

> `X`가 표본공간 `S`에서 정의된 확률변수이면:
>
> ```
> V(X) = E(X²) - E(X)²
> ```

### 증명

```
V(X) = Σ (X(s) - E(X))² · p(s)
     = Σ (X(s)² - 2·E(X)·X(s) + E(X)²) · p(s)       — (a-b)² 전개
     = Σ X(s)²·p(s) - 2·E(X)·Σ X(s)·p(s) + E(X)²·Σ p(s) — 합 분배
     = E(X²) - 2·E(X)·E(X) + E(X)²·1                 — Σp(s)=1
     = E(X²) - 2·E(X)² + E(X)²
     = E(X²) - E(X)²
```

### Lean 4로 표현

```lean
/-- V(X) = E(X²) - E(X)² 의 간소화된 버전 -/
def variance' (n : ℕ) (p X : Fin n → ℚ) : ℚ :=
  let eX2 := ∑ s : Fin n, p s * (X s)^2     -- E(X²)
  let eX  := ∑ s : Fin n, p s * X s          -- E(X)
  eX2 - eX^2
```

>  **실전 팁**: 분산을 구할 때는 항상 `V(X) = E(X²) - E(X)²` 공식을 사용하자!

---

## 10E.4 예제 14: 베르누이 시행의 분산

### 📋 문제

성공 확률 `p`, 실패 확률 `q = 1-p`. 성공이면 `X(t) = 1`, 실패이면 `X(t) = 0`인 확률변수 `X`의 분산은?

### 풀이

`X²(t) = X(t)`이므로 (0²=0, 1²=1):

```
V(X) = E(X²) - E(X)² = E(X) - E(X)² = p - p² = p(1 - p) = pq
```

```lean
-- p = 1/2: V(X) = (1/2)(1/2) = 1/4
example : (1/2 : ℚ) * (1 - 1/2) = 1/4 := by norm_num

-- p = 1/3: V(X) = (1/3)(2/3) = 2/9
example : (1/3 : ℚ) * (1 - 1/3) = 2/9 := by norm_num
```

---

## 10E.5 예제 15: 주사위의 분산

`E(X) = 7/2`. `E(X²)` 계산:

```
E(X²) = (1 + 4 + 9 + 16 + 25 + 36)/6 = 91/6
V(X) = 91/6 - (7/2)² = 91/6 - 49/4 = 35/12
```

```lean
example : (91/6 : ℚ) - (7/2)^2 = 35/12 := by norm_num
```

---

## 10E.6 정리 7: 비에나메의 공식 

###  정리 7 (비에나메의 공식)

> `X`와 `Y`가 표본공간 `S`에서 정의된 두 개의 **독립적**(independent) 확률변수라면:
>
> ```
> V(X + Y) = V(X) + V(Y)
> ```
>
> `n`개에 대해서 `Xᵢ`가 쌍으로 독립적일 때:
> ```
> V(X₁ + X₂ + ... + Xₙ) = V(X₁) + V(X₂) + ... + V(Xₙ)
> ```

 기댓값의 선형성은 독립이 **아니어도** 성립했지만, 분산은 **독립일 때만** 성립한다!

### 증명 아이디어

```
V(X+Y) = E((X+Y)²) - E(X+Y)²
       = E(X²+2XY+Y²) - (E(X)+E(Y))²
       = E(X²) + 2E(XY) + E(Y²) - E(X)² - 2E(X)E(Y) - E(Y)²
```

독립이므로 `E(XY) = E(X)E(Y)`:

```
       = (E(X²)-E(X)²) + (E(Y²)-E(Y)²) = V(X) + V(Y)
```

### 응용: n번 베르누이 시행의 분산

각 `Xᵢ`의 분산 = `pq`. 비에나메의 공식에 의해: **V(X) = npq**

```lean
-- n=100, p=1/2: V(X) = 100·(1/2)·(1/2) = 25
example : 100 * (1/2 : ℚ) * (1/2) = 25 := by norm_num

-- n=36, p=1/6: V(X) = 36·(1/6)·(5/6) = 5
example : 36 * (1/6 : ℚ) * (5/6) = 5 := by norm_num
```

---

## 10E.7 체비쇼프 부등식 

###  정리 8 (체비쇼프 부등식)

> **표본공간**(sample space) `S`에서 확률 함수 `p`인 확률변수 `X`, `r`이 양의 실수이면:
>
> ```
> p(|X(s) - E(X)| ≥ r) ≤ V(X) / r²
> ```

###  직관: "확률변수가 평균에서 `r` 이상 떨어질 확률은 `V(X)/r²` 이하이다."

### 증명

`A = {s ∈ S | |X(s) - E(X)| ≥ r}` 이라 하면:

```
V(X) = Σ_{s∈S} (X(s)-E(X))²·p(s)
     ≥ Σ_{s∈A} (X(s)-E(X))²·p(s)    (나머지 항 ≥ 0 이므로)
     ≥ Σ_{s∈A} r²·p(s)              (A에서 (X-E(X))² ≥ r²)
     = r²·p(A)
```

따라서 `p(A) ≤ V(X)/r²`.

### 예제 19: 동전 뒷면 횟수의 편차

동전 `n`번: `E(X) = n/2`, `V(X) = n/4`, `r = √n` 적용:

```
p(|X - n/2| ≥ √n) ≤ (n/4)/n = 1/4
```

```lean
-- n=100: r=10, V=25
-- p(|X-50| ≥ 10) ≤ 25/100 = 1/4
example : (25 : ℚ) / 100 = 1/4 := by norm_num
```

### 예제 20: 체비쇼프의 한계

```lean
-- 주사위: V(X)=35/12, r=3
-- p(|X-7/2| ≥ 3) ≤ 35/108 ≈ 0.324
-- 실제 확률은 0! (X∈{1,...,6}이므로 |X-3.5|<3)
example : (35/12 : ℚ) / 3^2 = 35/108 := by norm_num
```

>  체비쇼프는 **모든** 확률변수에 적용 가능하지만, 그만큼 **느슨**할 수 있다.

---

##  연습문제 — 설명형 예제

### 연습 1: 동전 10번 분산

> 동전을 10번 던져 앞면 횟수의 분산은? (Rosen 연습문제 27)

```lean
-- V(X) = npq = 10·(1/2)·(1/2) = 5/2
example : 10 * (1/2 : ℚ) * (1/2) = 5/2 := by norm_num
```

### 연습 2: 주사위 10번 분산

> 주사위 10번 던져 6이 나온 횟수의 분산은? (연습문제 28)

```lean
-- V(X) = 10·(1/6)·(5/6) = 25/18
example : 10 * (1/6 : ℚ) * (5/6) = 25/18 := by norm_num
```

---

##  연습문제 — 괄호 채우기 (skeleton)

### 연습 3: V(X) = E(X²) - E(X)² 적용

> 주사위 2배 확률변수 X (값: 2,4,6,8,10,12, 각 1/6)의 분산은?

```lean
-- E(X) = 7, E(X²) = (4+16+36+64+100+144)/6
example : (4 + 16 + 36 + 64 + 100 + 144 : ℚ) / 6 = (⟨채우세요⟩) := by norm_num
-- V(X) = E(X²) - E(X)²
example : (⟨E(X²)⟩ : ℚ) - 7^2 = (⟨채우세요⟩) := by norm_num
```

<details>
<summary> 답 보기</summary>

```lean
example : (4 + 16 + 36 + 64 + 100 + 144 : ℚ) / 6 = 182/3 := by norm_num
example : (182/3 : ℚ) - 7^2 = 35/3 := by norm_num
```

</details>

### 연습 4: 비에나메 적용

> n=20, p=1/4인 베르누이의 분산은?

```lean
example : 20 * (1/4 : ℚ) * (⟨q를 채우세요⟩) = (⟨답⟩) := by norm_num
```

<details>
<summary> 답 보기</summary>

```lean
example : 20 * (1/4 : ℚ) * (3/4) = 15/4 := by norm_num
```

</details>

### 연습 5: 체비쇼프 적용

> 동전 100번. 앞면이 50에서 15 이상 떨어질 확률의 상계는?

```lean
-- V = 25, r = 15
example : (25 : ℚ) / 15^2 = (⟨채우세요⟩) := by norm_num
```

<details>
<summary> 답 보기</summary>

```lean
example : (25 : ℚ) / 15^2 = 1/9 := by norm_num
-- 약 11% 이하
```

</details>

### 연습 6: 편향 동전 체비쇼프

> 앞면 확률 0.6. p·q/25 를 구하라.

```lean
example : (3/5 : ℚ) * (2/5) / 25 = (⟨채우세요⟩) := by norm_num
```

<details>
<summary> 답 보기</summary>

```lean
example : (3/5 : ℚ) * (2/5) / 25 = 6/625 := by norm_num
-- 약 0.96% 이하
```

</details>

---

##  연습문제 — sorry로 직접 증명하기

### 연습 7: (a - b)² 전개

```lean
example (a b : ℚ) : (a - b)^2 = a^2 - 2*a*b + b^2 := by sorry
```

<details>
<summary> 답 보기</summary>

```lean
example (a b : ℚ) : (a - b)^2 = a^2 - 2*a*b + b^2 := by ring
```

</details>

### 연습 8: 상수 합 = 상수 × 1

```lean
example (n : ℕ) (p : Fin n → ℚ) (b : ℚ) (h : ∑ s : Fin n, p s = 1) :
    ∑ s : Fin n, b * p s = b := by sorry
```

<details>
<summary> 답 보기</summary>

```lean
example (n : ℕ) (p : Fin n → ℚ) (b : ℚ) (h : ∑ s : Fin n, p s = 1) :
    ∑ s : Fin n, b * p s = b := by
  rw [← Finset.mul_sum, h, mul_one]
```

</details>

### 연습 9: 분산이 비음수

```lean
example (n : ℕ) (p X : Fin n → ℚ) (μ : ℚ) (hp : ∀ s, 0 ≤ p s) :
    0 ≤ ∑ s : Fin n, (X s - μ)^2 * p s := by sorry
```

<details>
<summary> 답 보기</summary>

```lean
example (n : ℕ) (p X : Fin n → ℚ) (μ : ℚ) (hp : ∀ s, 0 ≤ p s) :
    0 ≤ ∑ s : Fin n, (X s - μ)^2 * p s := by
  apply Finset.sum_nonneg
  intro s _
  exact mul_nonneg (sq_nonneg _) (hp s)
```

</details>

### 연습 10: 체비쇼프 수치

> n=400 동전. r=20. 상계는?

```lean
example : (100 : ℚ) / 20^2 = 1/4 := by sorry
```

<details>
<summary> 답 보기</summary>

```lean
example : (100 : ℚ) / 20^2 = 1/4 := by norm_num
```

</details>

### 연습 11: ring 연습

```lean
example (a b : ℚ) : a^2 - 2*a*b + b^2 = (a - b)^2 := by sorry
```

<details>
<summary> 답 보기</summary>

```lean
example (a b : ℚ) : a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
```

</details>

### 연습 12: 체비쇼프 또 다른 계산

```lean
example : (35/12 : ℚ) / (5/2)^2 = 7/15 := by sorry
```

<details>
<summary> 답 보기</summary>

```lean
example : (35/12 : ℚ) / (5/2)^2 = 7/15 := by norm_num
```

</details>

---

## 이 파트의 요약

| 개념 | 공식 / 설명 |
|---|---|
| **분산**(variance) | V(X) = E(X²) - E(X)² |
| **표준편차**(standard deviation) | σ(X) = √V(X) |
| **베르누이 분산** | V(X) = pq (단일), npq (n번) |
| **비에나메의 공식** | V(X+Y) = V(X)+V(Y) (독립) |
| **체비쇼프 부등식** | p(|X-E(X)| ≥ r) ≤ V(X)/r² |
| Lean `ring` | 다항식 등식 자동 증명 |
| Lean `sq_nonneg` | x² ≥ 0 |
| Lean `Finset.sum_nonneg` | 각 항 ≥ 0이면 합 ≥ 0 |

---

##  Part 10 시리즈 완결 요약

| 파트 | 주제 | 핵심 개념 |
|---|---|---|
| **10-A** | 이산확률 도입 (§7.1) | 표본공간, 사건, 라플라스 확률, 여사건, 합사건 |
| **10-B** | 확률론 (§7.2) | 확률분포, 조건부확률, 독립, 베르누이, 이항분포 |
| **10-C** | 베이즈 정리 (§7.3) | 베이즈 정리, 의학검사, 베이지안 스팸 필터 |
| **10-D** | 기댓값 (§7.4.1~7.4.6) | 기댓값, 선형성, 기하분포, 독립 확률변수 |
| **10-E** | 분산과 체비쇼프 (§7.4.7~7.4.8) | 분산, 비에나메 공식, 체비쇼프 부등식 |

>  Rosen 이산수학 7장 "이산확률"의 모든 내용을 Lean 4로 형식화하는 여정이 완료되었다!
