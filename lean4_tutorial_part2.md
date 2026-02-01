# Lean4 완전 정복 가이드 — 제2편

## 기본 데이터 타입 완전 정복

---

# 제2편: 데이터 타입의 세계

---

## 2.1 타입(Type)이란?

### 타입 = 데이터의 종류

**타입**은 "이 데이터가 어떤 종류인가"를 알려준다.

일상생활 비유:
```
"42"가 뭐야?
  → 숫자야 (Nat 타입)

"hello"가 뭐야?
  → 글자야 (String 타입)

"true"가 뭐야?
  → 참/거짓이야 (Bool 타입)
```

### 왜 타입이 필요해?

타입이 있으면 **말도 안 되는 연산을 막을 수 있다**:

```lean
-- 이건 된다
#eval 3 + 5      -- 숫자 + 숫자 = OK

-- 이건 안 된다 (Lean이 막아준다)
-- #eval 3 + "hello"   -- 숫자 + 글자 = 오류!
```

**타입 = 안전장치**

컴파일러가 "이 연산이 말이 되나?"를 미리 확인해준다.

---

## 2.2 Nat — 자연수

### Nat이 뭐야?

**Nat** = Natural numbers = 자연수 = {0, 1, 2, 3, 4, ...}

```lean
#check Nat    -- Nat : Type
#check 0      -- 0 : Nat
#check 42     -- 42 : Nat
#check 12345  -- 12345 : Nat
```

### 자연수 연산들

```lean
-- 덧셈
#eval 2 + 3      -- 5
```
```
설명: 2 더하기 3은 5
```

```lean
-- 뺄셈 (주의!)
#eval 5 - 3      -- 2
#eval 3 - 5      -- 0  (음수가 없다!)
```
```
⚠️ 주의: Nat에는 음수가 없다!
3 - 5는 원래 -2지만, Nat에서는 0이 된다.
이걸 "truncated subtraction"(잘린 뺄셈)이라고 한다.
```

```lean
-- 곱셈
#eval 4 * 5      -- 20
```

```lean
-- 나눗셈 (정수 나눗셈)
#eval 10 / 3     -- 3
#eval 7 / 2      -- 3
```
```
설명: 소수점 아래는 버린다
10 ÷ 3 = 3.333... → 3
7 ÷ 2 = 3.5 → 3
```

```lean
-- 나머지
#eval 10 % 3     -- 1
#eval 7 % 2      -- 1
```
```
설명: 나눈 나머지
10 = 3 × 3 + 1 → 나머지 1
7 = 2 × 3 + 1 → 나머지 1
```

```lean
-- 거듭제곱
#eval 2 ^ 10     -- 1024
```
```
설명: 2의 10승 = 1024
```

### 연산자 정리표

| 연산자 | 의미 | 예시 | 결과 |
|--------|------|------|------|
| `+` | 덧셈 | `3 + 4` | `7` |
| `-` | 뺄셈 (잘림) | `3 - 5` | `0` |
| `*` | 곱셈 | `3 * 4` | `12` |
| `/` | 나눗셈 (정수) | `7 / 2` | `3` |
| `%` | 나머지 | `7 % 2` | `1` |
| `^` | 거듭제곱 | `2 ^ 3` | `8` |

---

### Nat의 내부 구조 (귀납적 정의)

**이 부분은 좀 어려우니 천천히 읽자!**

Lean에서 자연수는 이렇게 정의되어 있다:

```lean
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
```

**한 줄씩 뜯어보자:**

```
inductive Nat where
    ↑
    "Nat을 귀납적으로 정의한다"
```

```
| zero : Nat
    ↑
    "zero(0)는 Nat이다"
```

```
| succ (n : Nat) : Nat
    ↑
    "n이 Nat이면, succ n (n의 다음 수)도 Nat이다"
```

### 숫자를 이 정의로 표현하면?

```
0 = zero
1 = succ zero           (0의 다음)
2 = succ (succ zero)    (1의 다음)
3 = succ (succ (succ zero))  (2의 다음)
...
```

**시각화:**
```
0:  zero
    
1:  succ ─── zero

2:  succ ─── succ ─── zero

3:  succ ─── succ ─── succ ─── zero
```

### 왜 이렇게 복잡하게 정의해?

이 정의 방식 덕분에 **귀납법**(induction)을 쓸 수 있다!

```
"모든 자연수에 대해 P가 성립한다"를 증명하려면:
1. P(zero)가 성립함을 보인다 (기저)
2. P(n) → P(succ n)임을 보인다 (귀납)

그러면 자동으로:
P(0) ✓
P(0) → P(1) 이므로 P(1) ✓
P(1) → P(2) 이므로 P(2) ✓
...
모든 자연수에 대해 P 성립! ✓
```

---

## 2.3 Bool — 참과 거짓

### Bool이 뭐야?

**Bool** = Boolean = 참/거짓 = {true, false}

```lean
#check Bool    -- Bool : Type
#check true    -- true : Bool
#check false   -- false : Bool
```

### Bool은 딱 2개의 값만 있다

```lean
inductive Bool where
  | false : Bool
  | true : Bool
```

이게 전부다! `true` 아니면 `false`.

### Bool 연산들

#### (1) `&&` — AND (그리고)

```lean
#eval true && true    -- true
#eval true && false   -- false
#eval false && true   -- false
#eval false && false  -- false
```

**진리표:**
| A | B | A && B |
|---|---|--------|
| true | true | true |
| true | false | false |
| false | true | false |
| false | false | false |

**일상 비유:**
```
"비가 오고(&&) 우산이 있다" → 둘 다 참이어야 참
```

#### (2) `||` — OR (또는)

```lean
#eval true || true    -- true
#eval true || false   -- true
#eval false || true   -- true
#eval false || false  -- false
```

**진리표:**
| A | B | A \|\| B |
|---|---|----------|
| true | true | true |
| true | false | true |
| false | true | true |
| false | false | false |

**일상 비유:**
```
"비가 오거나(||) 눈이 온다" → 하나만 참이어도 참
```

#### (3) `!` — NOT (부정)

```lean
#eval !true    -- false
#eval !false   -- true
```

**진리표:**
| A | !A |
|---|-----|
| true | false |
| false | true |

**일상 비유:**
```
"비가 안(!) 온다" → 참이면 거짓, 거짓이면 참
```

#### (4) `==` — 같은지 비교

```lean
#eval 3 == 3     -- true
#eval 3 == 5     -- false
#eval "a" == "a" -- true
#eval "a" == "b" -- false
```

#### (5) `!=` — 다른지 비교

```lean
#eval 3 != 5     -- true
#eval 3 != 3     -- false
```

#### (6) `<`, `<=`, `>`, `>=` — 크기 비교

```lean
#eval 3 < 5      -- true
#eval 5 < 3      -- false
#eval 3 <= 3     -- true
#eval 5 > 3      -- true
#eval 5 >= 5     -- true
```

### 연산자 정리표

| 연산자 | 의미 | 예시 | 결과 |
|--------|------|------|------|
| `&&` | AND | `true && false` | `false` |
| `\|\|` | OR | `true \|\| false` | `true` |
| `!` | NOT | `!true` | `false` |
| `==` | 같다 | `3 == 3` | `true` |
| `!=` | 다르다 | `3 != 5` | `true` |
| `<` | 작다 | `3 < 5` | `true` |
| `<=` | 작거나 같다 | `3 <= 3` | `true` |
| `>` | 크다 | `5 > 3` | `true` |
| `>=` | 크거나 같다 | `5 >= 5` | `true` |

---

## 2.4 String — 문자열

### String이 뭐야?

**String** = 문자열 = 글자들의 나열

```lean
#check String     -- String : Type
#check "hello"    -- "hello" : String
#check ""         -- "" : String (빈 문자열)
#check "123"      -- "123" : String (숫자도 따옴표 안에 있으면 문자열!)
```

### String 연산들

#### (1) `++` — 문자열 이어붙이기

```lean
#eval "Hello, " ++ "World!"    -- "Hello, World!"
#eval "abc" ++ "def"           -- "abcdef"
#eval "" ++ "hi"               -- "hi"
```

```
설명: 두 문자열을 앞뒤로 붙인다
"Hello, " ++ "World!" = "Hello, World!"
```

#### (2) `.length` — 길이

```lean
#eval "hello".length    -- 5
#eval "".length         -- 0
#eval "Lean4".length    -- 5
```

#### (3) 문자열 비교

```lean
#eval "abc" == "abc"    -- true
#eval "abc" == "ABC"    -- false (대소문자 구분!)
#eval "apple" < "banana"  -- true (사전순)
```

---

## 2.5 List — 리스트

### List가 뭐야?

**List** = 같은 타입의 값들을 순서대로 나열한 것

```lean
#check List Nat       -- List Nat : Type
#check [1, 2, 3]      -- [1, 2, 3] : List Nat
#check ["a", "b"]     -- ["a", "b"] : List String
#check ([] : List Nat)  -- [] : List Nat (빈 리스트)
```

**주의:** 리스트 안의 원소들은 **모두 같은 타입**이어야 한다!

```lean
-- 이건 안 된다!
-- #check [1, "hello", true]   -- 오류! 타입이 섞여 있음
```

### List 연산들

#### (1) `++` — 리스트 이어붙이기

```lean
#eval [1, 2] ++ [3, 4]      -- [1, 2, 3, 4]
#eval [1] ++ [2] ++ [3]     -- [1, 2, 3]
#eval [] ++ [1, 2]          -- [1, 2]
```

#### (2) `.length` — 길이

```lean
#eval [1, 2, 3].length      -- 3
#eval [].length             -- 0
#eval ["a", "b"].length     -- 2
```

#### (3) `.head?` — 첫 번째 원소

```lean
#eval [1, 2, 3].head?       -- some 1
#eval ([] : List Nat).head? -- none
```

```
설명: 
- 원소가 있으면 "some 값" 반환
- 빈 리스트면 "none" 반환
- ?가 붙은 건 "실패할 수도 있다"는 의미
```

#### (4) `.tail?` — 첫 번째 빼고 나머지

```lean
#eval [1, 2, 3].tail?       -- some [2, 3]
#eval [1].tail?             -- some []
#eval ([] : List Nat).tail? -- none
```

#### (5) `.reverse` — 뒤집기

```lean
#eval [1, 2, 3].reverse     -- [3, 2, 1]
#eval ["a", "b", "c"].reverse  -- ["c", "b", "a"]
```

#### (6) `.map` — 각 원소에 함수 적용

```lean
#eval [1, 2, 3].map (fun x => x * 2)     -- [2, 4, 6]
#eval [1, 2, 3].map (fun x => x + 10)    -- [11, 12, 13]
#eval ["hi", "bye"].map (fun s => s.length)  -- [2, 3]
```

```
설명:
[1, 2, 3].map (fun x => x * 2)

각 원소에 "x * 2" 적용:
  1 → 1 * 2 = 2
  2 → 2 * 2 = 4
  3 → 3 * 2 = 6

결과: [2, 4, 6]
```

#### (7) `.filter` — 조건에 맞는 것만 남기기

```lean
#eval [1, 2, 3, 4, 5].filter (fun x => x > 2)   -- [3, 4, 5]
#eval [1, 2, 3, 4, 5].filter (fun x => x % 2 == 0)  -- [2, 4]
```

```
설명:
[1, 2, 3, 4, 5].filter (fun x => x > 2)

각 원소가 조건 "x > 2"를 만족하는지:
  1 > 2? false → 버림
  2 > 2? false → 버림
  3 > 2? true → 남김
  4 > 2? true → 남김
  5 > 2? true → 남김

결과: [3, 4, 5]
```

#### (8) `::` — 맨 앞에 원소 추가

```lean
#eval 0 :: [1, 2, 3]        -- [0, 1, 2, 3]
#eval "a" :: ["b", "c"]     -- ["a", "b", "c"]
```

```
설명: "::"는 "cons"라고 읽는다
0 :: [1, 2, 3] = [0, 1, 2, 3]

맨 앞에 0을 붙인다
```

### 리스트 연산 정리표

| 연산 | 의미 | 예시 | 결과 |
|------|------|------|------|
| `++` | 이어붙이기 | `[1,2] ++ [3]` | `[1,2,3]` |
| `.length` | 길이 | `[1,2,3].length` | `3` |
| `.head?` | 첫 원소 | `[1,2].head?` | `some 1` |
| `.tail?` | 나머지 | `[1,2].tail?` | `some [2]` |
| `.reverse` | 뒤집기 | `[1,2,3].reverse` | `[3,2,1]` |
| `.map f` | 함수 적용 | `[1,2].map (·*2)` | `[2,4]` |
| `.filter p` | 필터링 | `[1,2,3].filter (·>1)` | `[2,3]` |
| `::` | 앞에 추가 | `0 :: [1,2]` | `[0,1,2]` |

---

### List의 내부 구조 (귀납적 정의)

```lean
inductive List (α : Type) where
  | nil : List α                      -- 빈 리스트
  | cons : α → List α → List α        -- 원소 하나 + 나머지 리스트
```

**한 줄씩 뜯어보자:**

```
inductive List (α : Type) where
             ↑
             α는 "아무 타입"을 의미
             List Nat, List String, List Bool 등 다 가능
```

```
| nil : List α
    ↑
    "빈 리스트 []는 List α다"
```

```
| cons : α → List α → List α
    ↑
    "a가 α 타입이고, as가 List α이면,
     cons a as (a를 맨 앞에 붙인 리스트)도 List α다"
```

### 리스트를 이 정의로 표현하면?

```
[]        = nil
[1]       = cons 1 nil
[1, 2]    = cons 1 (cons 2 nil)
[1, 2, 3] = cons 1 (cons 2 (cons 3 nil))
```

**`::` 기호를 쓰면:**
```
[1, 2, 3] = 1 :: 2 :: 3 :: []
          = 1 :: (2 :: (3 :: []))
```

**시각화:**
```
[1, 2, 3]:

  cons ─┬─ 1
        │
        └─ cons ─┬─ 2
                 │
                 └─ cons ─┬─ 3
                          │
                          └─ nil
```

---

## 2.6 함수 타입 α → β

### 함수 타입이 뭐야?

`**α → β**`는 "**α 타입의 값을 받아서 β 타입의 값을 돌려주는 함수**"의 타입이다.

```lean
#check Nat → Nat          -- Nat → Nat : Type
#check Nat → Bool         -- Nat → Bool : Type
#check String → Nat       -- String → Nat : Type
#check Nat → Nat → Nat    -- Nat → Nat → Nat : Type
```

### 예시로 이해하기

```lean
-- "자연수를 받아서 자연수를 돌려주는 함수"
def double : Nat → Nat := fun x => x * 2

#check double    -- double : Nat → Nat
#eval double 5   -- 10
```

```
해석:
double의 타입: Nat → Nat
  입력: Nat (자연수)
  출력: Nat (자연수)

double의 정의: fun x => x * 2
  "x를 받아서 x * 2를 돌려줘"
  
double 5:
  x = 5 대입
  5 * 2 = 10 반환
```

```lean
-- "자연수를 받아서 Bool을 돌려주는 함수"
def isEven : Nat → Bool := fun x => x % 2 == 0

#check isEven    -- isEven : Nat → Bool
#eval isEven 4   -- true
#eval isEven 5   -- false
```

```
해석:
isEven의 타입: Nat → Bool
  입력: Nat (자연수)
  출력: Bool (참/거짓)

isEven의 정의: fun x => x % 2 == 0
  "x를 받아서 x % 2 == 0의 결과를 돌려줘"
  (짝수면 true, 홀수면 false)
```

### 여러 인자를 받는 함수

```lean
-- "두 개의 자연수를 받아서 자연수를 돌려주는 함수"
def add : Nat → Nat → Nat := fun x y => x + y

#check add       -- add : Nat → Nat → Nat
#eval add 3 5    -- 8
```

**타입 읽는 법:**
```
Nat → Nat → Nat

이건 사실:
Nat → (Nat → Nat)

"Nat을 받아서, (Nat을 받아서 Nat을 돌려주는 함수)를 돌려주는 함수"
```

**왜 이렇게 복잡해?**

이건 **커링(Currying)**이라는 개념이다:

```lean
#eval add 3 5    -- 8

-- 이건 사실 이렇게 동작한다:
-- (add 3) 5
-- 
-- add 3 : Nat → Nat  ("3을 더하는 함수"가 됨)
-- (add 3) 5 = 8      (그 함수에 5를 넣음)
```

```lean
-- 부분 적용
def add3 : Nat → Nat := add 3

#check add3      -- add3 : Nat → Nat
#eval add3 10    -- 13
#eval add3 100   -- 103
```

```
해석:
add3 = add 3 = "3을 더하는 함수"

add3 10 = 3 + 10 = 13
add3 100 = 3 + 100 = 103
```

---

## 2.7 람다 표현식 (익명 함수)

### 람다가 뭐야?

**람다**(lambda)는 "이름 없는 함수"를 만드는 방법이다.

```lean
-- 이름 있는 함수
def double (x : Nat) : Nat := x * 2

-- 이름 없는 함수 (람다)
#check (fun x => x * 2)         -- Nat → Nat
#check (fun x : Nat => x * 2)   -- Nat → Nat (타입 명시)
```

### 람다 문법

```
fun 인자 => 본문

fun x => x * 2
 ↑   ↑      ↑
 │   │      └── 결과: x * 2를 계산해서 돌려줌
 │   └── 인자: x를 받음
 └── 키워드: "함수를 만든다"
```

### 람다 사용 예시

```lean
-- 바로 적용
#eval (fun x => x * 2) 5        -- 10
#eval (fun x => x + 100) 7      -- 107
#eval (fun s => s ++ "!") "Hi"  -- "Hi!"
```

```
(fun x => x * 2) 5

1. fun x => x * 2 는 "x를 받아서 x*2를 돌려주는 함수"
2. 이 함수에 5를 넣는다
3. x = 5 대입: 5 * 2 = 10
```

```lean
-- map과 함께 사용
#eval [1, 2, 3].map (fun x => x * 2)      -- [2, 4, 6]
#eval [1, 2, 3].map (fun x => x * x)      -- [1, 4, 9]
#eval ["a", "b"].map (fun s => s ++ s)    -- ["aa", "bb"]
```

### 축약 문법: `·` (점)

`fun x => ...x...` 대신 `·`를 쓸 수 있다:

```lean
-- 이 둘은 같다
#eval [1, 2, 3].map (fun x => x * 2)   -- [2, 4, 6]
#eval [1, 2, 3].map (· * 2)            -- [2, 4, 6]

-- 이 둘도 같다
#eval [1, 2, 3].map (fun x => x + 10)  -- [11, 12, 13]
#eval [1, 2, 3].map (· + 10)           -- [11, 12, 13]

-- 이 둘도 같다
#eval [1, 2, 3].filter (fun x => x > 1)  -- [2, 3]
#eval [1, 2, 3].filter (· > 1)           -- [2, 3]
```

```
· 는 "여기에 인자가 들어간다"는 표시
(· * 2) = (fun x => x * 2)
(· + 10) = (fun x => x + 10)
(· > 1) = (fun x => x > 1)
```

---

## 2.8 곱타입 (Product Type) — α × β

### 곱타입이 뭐야?

`α × β`는 "**α 타입 값과 β 타입 값을 묶은 쌍(pair)**"의 타입이다.

```lean
#check Nat × String        -- Nat × String : Type
#check (3, "hello")        -- (3, "hello") : Nat × String
#check (true, 42)          -- (true, 42) : Bool × Nat
```

### 쌍 만들기

```lean
def myPair : Nat × String := (42, "answer")

#eval myPair    -- (42, "answer")
```

### 쌍에서 값 꺼내기

```lean
-- .1 또는 .fst: 첫 번째 원소
#eval (3, "hello").1       -- 3
#eval (3, "hello").fst     -- 3

-- .2 또는 .snd: 두 번째 원소
#eval (3, "hello").2       -- "hello"
#eval (3, "hello").snd     -- "hello"
```

```
(3, "hello")
  ↑      ↑
  │      └── .2 또는 .snd = "hello"
  └── .1 또는 .fst = 3
```

### 세 개 이상도 가능

```lean
#check (1, 2, 3)            -- Nat × Nat × Nat
#check (1, "a", true)       -- Nat × String × Bool

#eval (1, 2, 3).1           -- 1
#eval (1, 2, 3).2.1         -- 2
#eval (1, 2, 3).2.2         -- 3
```

```
(1, 2, 3)은 사실 (1, (2, 3))

.1 = 1
.2 = (2, 3)
.2.1 = 2
.2.2 = 3
```

---

## 2.9 Option 타입 — 있을 수도 없을 수도

### Option이 뭐야?

`Option α`는 "α 타입의 값이 있거나(`some`) 없거나(`none`)"를 표현한다.

```lean
#check Option Nat         -- Option Nat : Type
#check some 5             -- some 5 : Option Nat
#check (none : Option Nat)  -- none : Option Nat
```

### 왜 필요해?

"실패할 수 있는 연산"의 결과를 표현할 때!

```lean
-- 빈 리스트의 첫 원소는?
#eval [1, 2, 3].head?     -- some 1  (있음!)
#eval ([] : List Nat).head?  -- none  (없음!)
```

```
리스트가 비어있으면 "첫 원소"가 없다.
이걸 어떻게 표현하지?

Option을 사용!
- 있으면: some 값
- 없으면: none
```

### Option 정의

```lean
inductive Option (α : Type) where
  | none : Option α           -- 값 없음
  | some : α → Option α       -- 값 있음
```

### Option 다루기

```lean
-- 값 꺼내기 (기본값 제공)
#eval (some 5).getD 0        -- 5 (있으니까 5)
#eval (none : Option Nat).getD 0  -- 0 (없으니까 기본값 0)
```

```
.getD = "get with Default"
값이 있으면 그 값, 없으면 기본값 사용
```

---

## 2.10 타입 요약표

| 타입 | 의미 | 예시 값 |
|------|------|---------|
| `Nat` | 자연수 | `0, 1, 42, 100` |
| `Int` | 정수 | `-5, 0, 42` |
| `Bool` | 참/거짓 | `true, false` |
| `String` | 문자열 | `"hello", ""` |
| `List α` | α의 리스트 | `[1,2,3], []` |
| `α → β` | 함수 | `fun x => x+1` |
| `α × β` | 쌍 | `(3, "hi")` |
| `Option α` | 있거나 없거나 | `some 5, none` |

---

## 2.11 이 장의 핵심 요약

### 배운 타입들

1. **Nat** — 자연수 {0, 1, 2, ...}
   - 연산: `+`, `-`, `*`, `/`, `%`, `^`
   - 주의: 뺄셈은 0에서 멈춤

2. **Bool** — 참/거짓 {true, false}
   - 연산: `&&`, `||`, `!`
   - 비교: `==`, `!=`, `<`, `<=`, `>`, `>=`

3. **String** — 문자열
   - 연산: `++`, `.length`

4. **List** — 리스트
   - 연산: `++`, `::`, `.length`, `.map`, `.filter`, `.reverse`

5. **함수 α → β** — 함수 타입
   - 람다: `fun x => ...`
   - 축약: `(· + 1)`

6. **곱타입 α × β** — 쌍
   - 만들기: `(a, b)`
   - 꺼내기: `.1`, `.2`

7. **Option α** — 있거나 없거나
   - `some x`, `none`

### 핵심 개념

- **귀납적 정의**: `Nat`과 `List`는 "기저 + 재귀"로 정의됨
- **커링**: 여러 인자 함수는 "함수를 반환하는 함수"
- **람다**: 이름 없는 함수 `fun x => ...`

---

## 2.12 연습 문제

### 문제 1: 결과 예측하기

```lean
#eval 15 / 4
#eval 15 % 4
#eval 3 - 10
#eval [1,2,3] ++ [4,5]
#eval [1,2,3,4,5].filter (· > 2)
#eval [1,2,3].map (· * 10)
```

<details>
<summary>정답 보기</summary>

```
3        (15 ÷ 4 = 3.75 → 3)
3        (15 = 4×3 + 3)
0        (음수 없음, 0에서 멈춤)
[1,2,3,4,5]
[3,4,5]  (2보다 큰 것만)
[10,20,30]
```
</details>

### 문제 2: 함수 작성하기

"자연수를 받아서 제곱을 반환하는 함수"를 작성하라.

```lean
def square : Nat → Nat := sorry
-- #eval square 5 가 25가 되어야 함
```

<details>
<summary>정답 보기</summary>

```lean
def square : Nat → Nat := fun x => x * x
-- 또는
def square (x : Nat) : Nat := x * x
```
</details>

### 문제 3: 리스트 연산

`[1, 2, 3, 4, 5]`에서 짝수만 골라서 각각 제곱한 리스트를 만들어라.

```lean
#eval [1,2,3,4,5]. ???  -- [4, 16]이 되어야 함
```

<details>
<summary>정답 보기</summary>

```lean
#eval [1,2,3,4,5].filter (fun x => x % 2 == 0) |>.map (fun x => x * x)
-- 또는
#eval ([1,2,3,4,5].filter (· % 2 == 0)).map (· * ·)
-- 결과: [4, 16]
```
</details>

### 문제 4: 타입 적기

다음 각각의 타입을 적어라.

```lean
#check 42
#check [true, false]
#check ("hi", 3)
#check fun x => x + 1
#check [1,2,3].head?
```

<details>
<summary>정답 보기</summary>

```
42 : Nat
[true, false] : List Bool
("hi", 3) : String × Nat
fun x => x + 1 : Nat → Nat
[1,2,3].head? : Option Nat
```
</details>

---

