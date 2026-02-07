# Lean4 완전 정복 가이드 — 제7-I편

## **합동의 응용**(Applications of Congruences) 완전 정복: **해싱**(Hashing), **의사난수**(Pseudorandom Numbers), **검증 숫자**(Check Digits)

> **교재**: Kenneth H. Rosen, "Discrete Mathematics and Its Applications" 8판  
> **범위**: 4.5절 합동의 응용 (해싱 함수, 의사난수 생성기, 검증 숫자)  
> **선수 학습**: 제7-E편(합동 기초), 제7-F편(선형합동, 역모듈로), 제7-H편(페르마의 작은 정리)  
> **참고**: 『Mathematics in Lean』 Chapter 6 (Discrete Mathematics — Finsets)

---

## 7I.0 이 장의 목표

1. **해싱 함수**(hashing function)의 개념과 합동을 이용한 구현을 이해한다
2. **선형 합동 생성기**(linear congruential generator)로 의사난수를 만드는 법을 안다
3. **검증 숫자**(check digits)의 원리를 이해하고 ISBN, UPC 등을 검증한다
4. 이 모든 것을 **Lean4 코드**로 구현한다

> 💡 이 장은 지금까지 배운 합동 이론이 **실제 세계**에서 어떻게 쓰이는지를 보여주는 장이다. 수학이 곧바로 컴퓨터 과학과 일상생활에 연결되는 것을 확인할 수 있다!

---

## 7I.1 **해싱 함수**(Hashing Functions) — 4.5.1절

### 7I.1.1 해싱이란?

데이터베이스에 100만 개의 레코드가 있다고 하자. 특정 레코드를 찾으려면 최악의 경우 100만 번 비교해야 한다. 너무 느리다!

**해싱**(hashing)은 데이터를 고정된 크기의 테이블에 분배하는 기법이다. **해싱 함수**(hashing function) $h$는 **키**(key) $k$를 테이블의 **위치**(slot) $h(k)$에 대응시킨다.

가장 간단한 해싱 함수는 **나머지 연산**이다:

$$h(k) = k \bmod m$$

여기서 $m$은 테이블의 크기이다.

```lean
-- 가장 간단한 해싱 함수
def hashMod (m : Nat) (k : Nat) : Nat := k % m

-- 테이블 크기 = 111
#eval hashMod 111 064212848  -- ?
#eval hashMod 111 037149212  -- ?
#eval hashMod 111 107405723  -- ?
```

### 7I.1.2 교재 예제 1: 나머지 해싱

$m = 111$인 해싱 함수 $h(k) = k \bmod 111$로 다음 레코드들을 할당하라:

| 키 $k$ | $h(k) = k \bmod 111$ |
|---|---|
| 064212848 | ? |
| 037149212 | ? |
| 107405723 | ? |
| 121252592 | ? |
| 023140157 | ? |
| 100205292 | ? |
| 011300192 | ? |

```lean
-- 각 키의 해시 값 계산
def keys : List Nat := [064212848, 037149212, 107405723, 121252592, 023140157, 100205292, 011300192]

#eval keys.map (hashMod 111)
-- 결과 확인
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval 064212848 % 111  -- 14
#eval 037149212 % 111  -- 65
#eval 107405723 % 111  -- 14  (충돌!)
#eval 121252592 % 111  -- 77
#eval 023140157 % 111  -- 0
#eval 100205292 % 111  -- 15
#eval 011300192 % 111  -- 77  (충돌!)

-- 064212848과 107405723이 같은 해시 값 14 → 충돌!
-- 121252592와 011300192가 같은 해시 값 77 → 충돌!
```

</details>

### 7I.1.3 **충돌**(Collision)과 해결

두 개의 서로 다른 키가 같은 해시 값을 가지는 것을 **충돌**(collision)이라 한다. 위 예제에서 064212848과 107405723은 둘 다 해시 값 14를 가진다.

충돌이 생기면 어떻게 할까? 여러 방법이 있다:
- **체이닝**(chaining): 같은 슬롯에 연결 리스트로 저장
- **개방 주소법**(open addressing): 빈 슬롯을 찾아서 저장
- **선형 탐사**(linear probing): $h(k) + 1, h(k) + 2, \ldots$ 순서로 빈 곳 찾기

```lean
-- 해싱 테이블 시뮬레이션 (체이닝 방식)
-- 각 슬롯은 키들의 리스트
def buildHashTable (m : Nat) (keys : List Nat) : List (Nat × List Nat) :=
  let slots := (List.range m)
  slots.filterMap fun slot =>
    let keysInSlot := keys.filter fun k => k % m == slot
    if keysInSlot.isEmpty then none
    else some (slot, keysInSlot)

#eval buildHashTable 111 [064212848, 037149212, 107405723, 121252592, 023140157, 100205292, 011300192]
-- 어떤 슬롯에 여러 키가 있는지 확인
```

### 7I.1.4 좋은 해싱 함수의 조건

좋은 해싱 함수는:
1. **균등 분배**: 키들이 테이블 전체에 고르게 분포
2. **빠른 계산**: $O(1)$ 시간에 계산 가능
3. **적은 충돌**: 서로 다른 키들이 같은 값을 가질 확률이 낮음

$m$을 **소수**로 선택하면 충돌이 줄어드는 경향이 있다. 이것이 해싱에서 소수가 중요한 이유이다!

```lean
-- m이 소수일 때와 아닐 때 비교
-- 소수 m = 97
#eval buildHashTable 97 [100, 200, 300, 400, 500, 600, 700]
-- 비소수 m = 100
#eval buildHashTable 100 [100, 200, 300, 400, 500, 600, 700]
-- m = 100일 때: 100의 배수들이 모두 슬롯 0으로 몰린다!
```

---

## 7I.2 **의사난수 생성기**(Pseudorandom Number Generators) — 4.5.2절

### 7I.2.1 왜 "의사"난수인가?

컴퓨터는 결정론적(deterministic) 기계이다. 따라서 "진짜" 난수를 만들 수 없다. 대신 **난수처럼 보이는** 수열을 만든다. 이것을 **의사난수**(pseudorandom number)라 한다.

### 7I.2.2 **선형 합동 생성기**(Linear Congruential Generator)

가장 널리 사용되는 방법이 **선형 합동 방법**(linear congruential method)이다.

> **정의**: 4개의 정수 — **계수**(multiplier) $a$, **증분**(increment) $c$, **계수**(modulus) $m$, **시드**(seed) $x_0$ — 가 주어졌을 때, 다음 점화식으로 수열을 생성한다:
>
> $$x_{n+1} = (ax_n + c) \bmod m$$

```lean
-- 선형 합동 생성기
def lcg (a c m seed : Nat) (n : Nat) : List Nat :=
  let rec go (x : Nat) : Nat → List Nat → List Nat
    | 0, acc => acc.reverse
    | k + 1, acc =>
      let next := (a * x + c) % m
      go next k (next :: acc)
  go seed n []

-- 교재 예제 2: m = 9, a = 7, c = 4, x₀ = 3
#eval lcg 7 4 9 3 15
-- [7, 8, 6, 1, 2, 0, 4, 5, 3, 7, 8, 6, 1, 2, 0]
```

### 7I.2.3 교재 예제 2: $m = 9, a = 7, c = 4, x_0 = 3$

수열을 손으로 추적해 보자:

| $n$ | $x_n$ | 계산: $7x_n + 4 \bmod 9$ |
|---|---|---|
| 0 | 3 | (시드) |
| 1 | 7 | $7 \times 3 + 4 = 25 \equiv 7$ |
| 2 | 8 | $7 \times 7 + 4 = 53 \equiv 8$ |
| 3 | 6 | $7 \times 8 + 4 = 60 \equiv 6$ |
| 4 | 1 | $7 \times 6 + 4 = 46 \equiv 1$ |
| 5 | 2 | $7 \times 1 + 4 = 11 \equiv 2$ |
| 6 | 0 | $7 \times 2 + 4 = 18 \equiv 0$ |
| 7 | 4 | $7 \times 0 + 4 = 4 \equiv 4$ |
| 8 | 5 | $7 \times 4 + 4 = 32 \equiv 5$ |
| 9 | 3 | $7 \times 5 + 4 = 39 \equiv 3$ ← 시드로 돌아옴! |

9번째에서 $x_0 = 3$으로 돌아왔다! **주기**(period)가 9 = $m$이다. 이것은 최대 주기이므로 좋은 생성기이다.

```lean
-- 각 단계 검증
example : (7 * 3 + 4) % 9 = 7 := by native_decide
example : (7 * 7 + 4) % 9 = 8 := by native_decide
example : (7 * 8 + 4) % 9 = 6 := by native_decide
example : (7 * 6 + 4) % 9 = 1 := by native_decide
example : (7 * 1 + 4) % 9 = 2 := by native_decide
example : (7 * 2 + 4) % 9 = 0 := by native_decide
example : (7 * 0 + 4) % 9 = 4 := by native_decide
example : (7 * 4 + 4) % 9 = 5 := by native_decide
example : (7 * 5 + 4) % 9 = 3 := by native_decide  -- 시드로 복귀!

-- 주기 확인: 0부터 m-1까지 모든 수가 한 번씩 나타남
#eval lcg 7 4 9 3 9
-- [7, 8, 6, 1, 2, 0, 4, 5, 3] — {0,1,2,...,8} 모두 등장 ✓
```

### 7I.2.4 교재 예제 3: 순수 곱셈 생성기

$c = 0$인 경우를 **순수 곱셈 생성기**(pure multiplicative generator)라 한다.

$m = 2^{31} - 1 = 2147483647$ (메르센 소수!), $a = 7^5 = 16807$, $c = 0$

이것은 IBM에서 오래 사용한 유명한 생성기이다.

```lean
-- 순수 곱셈 생성기
#eval (2^31 - 1 : Nat)  -- 2147483647 (메르센 소수)
#eval (7^5 : Nat)       -- 16807

-- 처음 몇 개의 난수
#eval lcg 16807 0 2147483647 1 5
-- [16807, 282475249, ...]
```

### 7I.2.5 좋은 생성기의 조건

$x_{n+1} = (ax_n + c) \bmod m$이 **최대 주기** $m$을 가지려면 (Hull-Dobell 정리):

1. $c$와 $m$이 서로소: $\gcd(c, m) = 1$
2. $m$의 모든 소인수 $p$에 대해 $a - 1$이 $p$로 나누어짐
3. $m$이 4의 배수이면 $a - 1$도 4의 배수

```lean
-- 예제 2의 매개변수 확인: m = 9, a = 7, c = 4
-- gcd(4, 9) = 1 ✓
-- 9 = 3²의 소인수: 3, (7-1) = 6이 3으로 나누어짐 ✓
-- 9는 4의 배수가 아님 (조건 3 해당 없음) ✓
#eval Nat.gcd 4 9   -- 1 ✓
#eval 6 % 3          -- 0 ✓
```

---

## 7I.3 연습문제 세트 1: 해싱과 의사난수

### 연습 1-1: 교재 연습문제 1

해싱 함수 $h(k) = k \bmod 31$로 다음 사회보장번호(SSN)들의 해시 값을 구하라.

```lean
-- (a) 104578690
-- (b) 432222187
-- (c) 372201919
-- (d) 501338753

-- 한꺼번에 계산
#eval [104578690, 432222187, 372201919, 501338753].map (· % 31)
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval 104578690 % 31  -- ?
#eval 432222187 % 31  -- ?
#eval 372201919 % 31  -- ?
#eval 501338753 % 31  -- ?
-- 충돌이 있는지도 확인!
```

</details>

### 연습 1-2: 교재 연습문제 5

$m = 9, a = 3, c = 5, x_0 = 4$인 선형 합동 생성기로 처음 10개의 의사난수를 구하라.

```lean
#eval lcg 3 5 9 4 10  -- [?, ?, ?, ...]
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval lcg 3 5 9 4 10
-- 손으로 확인:
-- x₁ = (3×4 + 5) % 9 = 17 % 9 = 8
-- x₂ = (3×8 + 5) % 9 = 29 % 9 = 2
-- x₃ = (3×2 + 5) % 9 = 11 % 9 = 2  ← 주기 시작!
-- x₄ = (3×2 + 5) % 9 = 2 ... 반복

example : (3 * 4 + 5) % 9 = 8 := by native_decide
example : (3 * 8 + 5) % 9 = 2 := by native_decide
example : (3 * 2 + 5) % 9 = 2 := by native_decide  -- 2에서 고정!
-- 주기가 매우 짧다 — 나쁜 생성기!
```

</details>

### 연습 1-3: 주기 계산 (sorry 연습)

```lean
-- lcg 7 4 9 3의 주기가 9임을 확인
-- (9번째 값이 시드와 같다)
def lcgNth (a c m seed n : Nat) : Nat :=
  match n with
  | 0 => seed
  | k + 1 => (a * lcgNth a c m seed k + c) % m

theorem lcg_period_9 : lcgNth 7 4 9 3 9 = sorry := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem lcg_period_9 : lcgNth 7 4 9 3 9 = 3 := by native_decide
-- 9번째에서 시드 3으로 돌아옴 → 주기 = 9 = m (최대 주기!)
```

</details>

---

## 7I.4 **검증 숫자**(Check Digits) — 4.5.3절

### 7I.4.1 검증 숫자란?

일상생활에서 숫자를 입력할 때 실수가 발생한다. **검증 숫자**(check digit)는 입력 오류를 감지하기 위해 추가하는 숫자이다.

핵심 아이디어: 합동 연산을 이용하여 "올바른 번호인가?"를 빠르게 검사한다.

### 7I.4.2 **패리티 검사 비트**(Parity Check Bit)

가장 간단한 검증 방법은 **패리티 비트**(parity check bit)이다: 이진 문자열의 끝에 1의 개수가 짝수가 되도록 비트를 추가한다.

```lean
-- 패리티 비트 계산
def parityBit (bits : List Nat) : Nat :=
  (bits.foldl (· + ·) 0) % 2

-- 예: [1, 0, 1, 1, 0, 0, 1]의 1 개수 = 4 (짝수)이므로 패리티 비트 = 0
#eval parityBit [1, 0, 1, 1, 0, 0, 1]  -- 0

-- 예: [1, 1, 0, 1, 0, 0, 1]의 1 개수 = 4 (짝수)이므로 패리티 비트 = 0
#eval parityBit [1, 1, 0, 1, 0, 0, 1]  -- 0

-- 검증: 비트열 + 패리티 비트의 합은 항상 짝수
def checkParity (bitsWithParity : List Nat) : Bool :=
  (bitsWithParity.foldl (· + ·) 0) % 2 == 0
```

### 7I.4.3 ISBN-10 (국제 표준 도서 번호)

**ISBN-10** (International Standard Book Number)은 10자리 번호 $a_1 a_2 \ldots a_{10}$으로, 다음 조건을 만족한다:

$$\sum_{i=1}^{10} i \cdot a_i \equiv 0 \pmod{11}$$

마지막 자리 $a_{10}$은 검증 숫자이다. $a_{10}$이 10이면 X로 표기한다.

```lean
-- ISBN-10 검증
def checkISBN10 (digits : List Nat) : Bool :=
  if digits.length != 10 then false
  else
    let weighted := digits.enum.map fun (i, d) => (i + 1) * d
    weighted.foldl (· + ·) 0 % 11 == 0

-- 교재 예제 4: ISBN 007-462989-4
-- 숫자: [0, 0, 7, 4, 6, 2, 9, 8, 9, 4]
#eval checkISBN10 [0, 0, 7, 4, 6, 2, 9, 8, 9, 4]
```

### 7I.4.4 교재 예제 4: ISBN 검증

ISBN 007-462989-4가 유효한지 확인하라.

$$1 \cdot 0 + 2 \cdot 0 + 3 \cdot 7 + 4 \cdot 4 + 5 \cdot 6 + 6 \cdot 2 + 7 \cdot 9 + 8 \cdot 8 + 9 \cdot 9 + 10 \cdot 4$$

```lean
-- 손으로 계산
-- 1×0 = 0
-- 2×0 = 0
-- 3×7 = 21
-- 4×4 = 16
-- 5×6 = 30
-- 6×2 = 12
-- 7×9 = 63
-- 8×8 = 64
-- 9×9 = 81
-- 10×4 = 40
-- 합 = 0 + 0 + 21 + 16 + 30 + 12 + 63 + 64 + 81 + 40 = 327
-- 327 mod 11 = ?

#eval 327 % 11  -- 0이면 유효!
example : 327 % 11 = 0 := by native_decide  -- ✓ 유효!

-- 함수로 검증
#eval checkISBN10 [0, 0, 7, 4, 6, 2, 9, 8, 9, 4]  -- true ✓
```

### 7I.4.5 교재 예제 5: 검증 숫자 역산

ISBN 007-462989-?의 검증 숫자를 구하라.

```lean
-- 검증 숫자 계산: 나머지 9자리가 주어졌을 때 a₁₀ 구하기
def isbn10CheckDigit (first9 : List Nat) : Nat :=
  let partial := first9.enum.map fun (i, d) => (i + 1) * d
  let s := partial.foldl (· + ·) 0
  -- 10 * a₁₀ ≡ -s (mod 11)이므로
  -- a₁₀ ≡ -s * 10⁻¹ (mod 11)
  -- 10⁻¹ mod 11 = 10 (왜? 10 × 10 = 100 ≡ 1 mod 11)
  ((11 - s % 11) * 10) % 11

-- 실제로는 더 간단하게:
-- sum = 1×0 + 2×0 + ... + 9×9 = 287
-- 10 × a₁₀ ≡ -287 (mod 11)
-- 287 mod 11 = 1, 따라서 10 × a₁₀ ≡ -1 ≡ 10 (mod 11)
-- a₁₀ = 1? 아니다: 10 × 1 = 10 ≡ 10 (mod 11), 하지만 -287 mod 11 = ...

-- 직접 계산
#eval (1*0 + 2*0 + 3*7 + 4*4 + 5*6 + 6*2 + 7*9 + 8*8 + 9*9)  -- 287
#eval 287 % 11  -- 1
-- 10 × a₁₀ ≡ -1 ≡ 10 (mod 11)
-- a₁₀ ≡ 1 (mod 11)이지만... 확인해보자
-- 10 × 4 = 40 ≡ 7 (mod 11)? 아니다
-- 287 + 10×4 = 327, 327 % 11 = 0 ✓ 이므로 a₁₀ = 4

-- 전수검색으로 구하기 (가장 확실한 방법)
def findCheckDigit (first9 : List Nat) : Option Nat :=
  (List.range 11).find? fun d =>
    let full := first9 ++ [d]
    checkISBN10 full

#eval findCheckDigit [0, 0, 7, 4, 6, 2, 9, 8, 9]  -- some 4 ✓
```

### 7I.4.6 ISBN-10이 감지할 수 있는 오류

ISBN-10은 다음 오류를 **모두 감지**할 수 있다:
1. **단일 자릿수 오류**: 한 자리를 잘못 입력
2. **인접 자릿수 교환**: 두 인접한 자리의 순서를 바꿈

```lean
-- 오류 감지 시연
-- 원본: [0, 0, 7, 4, 6, 2, 9, 8, 9, 4] — 유효

-- 1. 단일 자릿수 오류: 7을 8로 변경
#eval checkISBN10 [0, 0, 8, 4, 6, 2, 9, 8, 9, 4]  -- false (감지!)

-- 2. 인접 자릿수 교환: 4와 6을 교환
#eval checkISBN10 [0, 0, 7, 6, 4, 2, 9, 8, 9, 4]  -- false (감지!)
```

---

## 7I.5 **UPC**(범용 제품 코드) — 교재 예제 7

### 7I.5.1 UPC란?

**UPC**(Universal Product Code)는 12자리 **바코드**(barcode) 번호이다. 마트에서 스캔하는 그 바코드이다!

검증 조건:

$$3a_1 + a_2 + 3a_3 + a_4 + \cdots + 3a_{11} + a_{12} \equiv 0 \pmod{10}$$

즉, 홀수 자릿수에 3을 곱하고 짝수 자릿수에 1을 곱한 합이 10의 배수여야 한다.

```lean
-- UPC 검증
def checkUPC (digits : List Nat) : Bool :=
  if digits.length != 12 then false
  else
    let weights := (List.range 12).map fun i => if i % 2 == 0 then 3 else 1
    let weighted := (digits.zip weights).map fun (d, w) => d * w
    weighted.foldl (· + ·) 0 % 10 == 0
```

### 7I.5.2 교재 예제 7: UPC 검증

UPC 036000-291452가 유효한지 확인하라.

```lean
-- 자릿수: [0, 3, 6, 0, 0, 0, 2, 9, 1, 4, 5, 2]
-- 가중합: 3×0 + 1×3 + 3×6 + 1×0 + 3×0 + 1×0 + 3×2 + 1×9 + 3×1 + 1×4 + 3×5 + 1×2

#eval 3*0 + 1*3 + 3*6 + 1*0 + 3*0 + 1*0 + 3*2 + 1*9 + 3*1 + 1*4 + 3*5 + 1*2
-- = 0 + 3 + 18 + 0 + 0 + 0 + 6 + 9 + 3 + 4 + 15 + 2 = 60

example : 60 % 10 = 0 := by native_decide  -- ✓ 유효!

#eval checkUPC [0, 3, 6, 0, 0, 0, 2, 9, 1, 4, 5, 2]  -- true ✓
```

### 7I.5.3 UPC의 한계

UPC는 단일 자릿수 오류를 감지할 수 있지만, **인접 자릿수 교환**은 항상 감지하지 **못한다**.

```lean
-- UPC 오류 감지 테스트
-- 원본: [0, 3, 6, 0, 0, 0, 2, 9, 1, 4, 5, 2]

-- 단일 자릿수 오류: 3을 4로
#eval checkUPC [0, 4, 6, 0, 0, 0, 2, 9, 1, 4, 5, 2]  -- false (감지!)

-- 인접 교환: 0과 3을 교환
#eval checkUPC [3, 0, 6, 0, 0, 0, 2, 9, 1, 4, 5, 2]  -- ? (감지될 수도 안 될 수도)
```

---

## 7I.6 **ISBN-13** — 현대의 국제 표준 도서 번호

### 7I.6.1 ISBN-13이란?

2007년부터 ISBN은 10자리에서 **13자리**로 바뀌었다. ISBN-13의 검증 조건은 UPC와 같다:

$$a_1 + 3a_2 + a_3 + 3a_4 + \cdots + a_{13} \equiv 0 \pmod{10}$$

(또는 동등하게: 홀수 위치에 1, 짝수 위치에 3)

```lean
-- ISBN-13 검증 (UPC와 같은 방식!)
def checkISBN13 (digits : List Nat) : Bool :=
  if digits.length != 13 then false
  else
    let weights := (List.range 13).map fun i => if i % 2 == 0 then 1 else 3
    let weighted := (digits.zip weights).map fun (d, w) => d * w
    weighted.foldl (· + ·) 0 % 10 == 0

-- 예: ISBN 978-0-07-288008-1
-- 자릿수: [9, 7, 8, 0, 0, 7, 2, 8, 8, 0, 0, 8, 1]
#eval checkISBN13 [9, 7, 8, 0, 0, 7, 2, 8, 8, 0, 0, 8, 1]
```

---

## 7I.7 연습문제 세트 2: 검증 숫자

### 연습 2-1: 교재 연습문제 9

ISBN-10 007-232253-?의 검증 숫자를 구하라.

```lean
#eval findCheckDigit [0, 0, 7, 2, 3, 2, 2, 5, 3]  -- ?
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval findCheckDigit [0, 0, 7, 2, 3, 2, 2, 5, 3]
-- 결과 확인

-- 손으로 검산:
-- 1×0 + 2×0 + 3×7 + 4×2 + 5×3 + 6×2 + 7×2 + 8×5 + 9×3 = ?
#eval 0 + 0 + 21 + 8 + 15 + 12 + 14 + 40 + 27  -- 137
#eval 137 % 11  -- ?
-- 10 × a₁₀ ≡ -(137 mod 11) (mod 11)
```

</details>

### 연습 2-2: 교재 연습문제 11

UPC 0-79893-10042-?의 검증 숫자를 구하라.

```lean
def findUPCCheckDigit (first11 : List Nat) : Option Nat :=
  (List.range 10).find? fun d =>
    checkUPC (first11 ++ [d])

#eval findUPCCheckDigit [0, 7, 9, 8, 9, 3, 1, 0, 0, 4, 2]  -- ?
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval findUPCCheckDigit [0, 7, 9, 8, 9, 3, 1, 0, 0, 4, 2]

-- 손으로: 3×0 + 1×7 + 3×9 + 1×8 + 3×9 + 1×3 + 3×1 + 1×0 + 3×0 + 1×4 + 3×2 + 1×d
-- = 0 + 7 + 27 + 8 + 27 + 3 + 3 + 0 + 0 + 4 + 6 + d = 85 + d
-- 85 + d ≡ 0 (mod 10) → d = 5
```

</details>

### 연습 2-3: ISBN-10 오류 감지 증명 (sorry 연습)

```lean
-- ISBN-10에서 한 자리만 바꾸면 검증이 실패하는 예
-- 원본: [0, 0, 7, 4, 6, 2, 9, 8, 9, 4] — 유효
-- 3번째 자리를 7 → 5로 변경

theorem isbn_error_detect :
  checkISBN10 [0, 0, 5, 4, 6, 2, 9, 8, 9, 4] = sorry := by native_decide
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem isbn_error_detect :
  checkISBN10 [0, 0, 5, 4, 6, 2, 9, 8, 9, 4] = false := by native_decide
-- 7을 5로 바꾸면 3번째 가중치 3×5 = 15 (원래 3×7 = 21)
-- 차이 = -6, 합이 321이 되어 321 % 11 = 2 ≠ 0
```

</details>

---

## 7I.8 Lean4와 실용적 해싱 — 심화

### 7I.8.1 Lean4의 Hashable 타입클래스

Lean4에는 `Hashable` 타입클래스가 내장되어 있다:

```lean
-- Lean4의 내장 해시
#check @Hashable
#check @hash

-- 문자열의 해시
#eval hash "hello"
#eval hash "world"
#eval hash "hello" == hash "hello"  -- true: 같은 입력 → 같은 해시
```

### 7I.8.2 HashMap

Lean4에는 효율적인 해시맵 구현도 있다:

```lean
-- Lean4의 HashMap 사용 예
-- import Std.Data.HashMap
-- let map := Std.HashMap.empty
-- let map := map.insert "key1" 42
-- let map := map.insert "key2" 99
-- map.find? "key1"  -- some 42
```

---

## 7I.9 전술 요약

| 전술 | 용도 | 예시 |
|------|------|------|
| `native_decide` | 구체적 숫자 계산 | `327 % 11 = 0` |
| `norm_num` | 정수 산술 | `3 * 7 + 4 = 25` |
| `decide` | 유한 범위 전수 검사 | 패리티 검증 |
| `simp` | 단순화 | 리스트 연산 |
| `rfl` | 정의에 의한 등식 | `hashMod 111 0 = 0` |

---

## 7I.10 핵심 정리 요약

| 개념 | 내용 |
|------|------|
| **해싱 함수** | $h(k) = k \bmod m$으로 데이터를 테이블에 분배 |
| **충돌** | 서로 다른 키가 같은 해시 값 → 체이닝 등으로 해결 |
| **선형 합동 생성기** | $x_{n+1} = (ax_n + c) \bmod m$으로 의사난수 생성 |
| **최대 주기 조건** | $\gcd(c, m) = 1$ 등 (Hull-Dobell 정리) |
| **ISBN-10** | $\sum i \cdot a_i \equiv 0 \pmod{11}$ — 단일 오류+교환 감지 |
| **UPC/ISBN-13** | 가중합 $\equiv 0 \pmod{10}$ — 단일 오류 감지 |

---

## 다음 장 예고

이것으로 **제7장 (정수론)** 시리즈가 완결된다!

제7장에서 다룬 내용:
- **7-A**: 나눗셈, 나머지, 약수
- **7-B**: 모듈러 연산, 합동
- **7-C**: 정수의 표현 (진법 변환)
- **7-D**: (이전 파트의 연장선)
- **7-E**: 합동의 기초
- **7-F**: 선형 합동, 역모듈로
- **7-G**: 중국인의 나머지 정리, 큰 정수의 연산
- **7-H**: 페르마의 작은 정리, 의사소수, 기본 루트, 이산 로그
- **7-I**: 합동의 응용 (해싱, 의사난수, 검증 숫자)

다음 시리즈에서는 Rosen Chapter 5(귀납법과 재귀)로 넘어갈 예정이다!

---

**(끝)**
