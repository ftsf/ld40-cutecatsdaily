import nico
import nico/vec
import algorithm
import sequtils
import strutils
import math
import tables
import astar
import hashes

{.this:self.}

# CONSTANTS

const friction = 0.25
const playerAccel = 10.0
const playerMaxSpeed = 2.0

const introText = [
  "WHAT'S THIS?",
  "A WINDOW POPPED UP OVER MY\nSOCIAL MEDIA FEED.",
  "WOW, IT SAYS: \"CUTE CATS\nDELIVERED TO YOUR FEED, DAILY!\"",
  "OH, IT WANTS MY ADDRESS\nWEIRD...",
  "WHATEVER,",
  "SUBSCRIBED!",
  "HUH? \"WE'VE JUST SENT\nYOU YOUR FIRST SHIPMENT\"...",
  "OHHH... I MISREAD.",
  "\"CUTE CATS DELIVERED\nTO YOU TO FEED, DAILY!\"",
  "I SEE...",
  "HMM, THE UNSUBSCRIBE\nBUTTON ISN'T WORKING...",
  "WHAT'S THAT AT THE DOOR?",
]

const noteText = [
  "HMM THERE'S A NOTE ATTACHED\nFIRST DAY!\nFREE FOOD SAMPLE INCLUDED!",
  "WE FORGOT:\nHERE'S SOME FREE LITTER\nAND A LITTER BOX!",
  "OK, YOU'RE ON YOUR OWN NOW.\nGO BUY SOME SUPPLIES\nFROM THE SHOPS.",
  "REMEMBER TO KEEP THE LITTER\nCLEAN. THROW OLD LITTER\nIN THE BIN.",
  "LEAVE YOUR BINS OUT ON\nTHURSDAY FOR COLLECTION.",
  "EACH DAY WE SEND $10\nFOR EACH CAT YOU'RE CARING FOR.",
  "WE ALSO ADD A BONuS $1\nFOR EACH DAY YOU ACCEPT A\nCAT IN A ROW.",
  "IF YOU LEAVE SOMETHING\nIN THE WAY WE WON'T\nDELIVER TODAY.",
  "IF YOUR HOUSE GETS TOO\nSMELLY, PEOPLE WILL COMPLAIN.\nYOU MAY LOSE YOUR HOUSE.",
  "ALSO, CATS DON'T LIKE\nA SMELLY HOUSE.\nKEEP THEM HAPPY!",
  "ONCE YOU HAVE HAD A\nCAT FOR 10 DAYS\nYOU CAN ADOPT IT OUT!",
  "TALK TO THE ADOPTION\nCENTRE ABOUT ADOPTING\nOUT CATS!",
]

const daysOfWeek = [
  "MON",
  "TUE",
  "WED",
  "THU",
  "FRI",
  "SAT",
  "SUN",
]

# TYPES

type Tile = tuple
  x,y: int
  t: uint8

type Tilemap = seq[seq[int]]

type Hitbox = tuple
  x,y,w,h: int

type Entity = ref object of RootObj
  toKill: bool
  pos: Vec2i
  offset: Vec2i
  hitbox: Hitbox

type Movable = ref object of Entity
  vel: Vec2f
  rem: Vec2f

type CatColor = enum
  Ginger = "ginger"
  White = "white"
  Black = "black"

type CatPersonality = enum
  Skittish = "skittish"
  Outgoing = "social"
  Dominant = "dominant"
  Spontaneous = "zaney"
  Friendly = "friendly"

type CatState = enum
  Chill
  Wander
  Hyper
  GoToToilet
  GoToEat
  Sleep

type Poop = ref object of Movable

type Wee = ref object of Entity
  age: int

type Bowl = ref object of Movable
  foodServes: int
  waterServes: int
  occupied: Entity

type LitterBox = ref object of Movable
  hasLitter: bool
  wee: int
  poop: int
  occupied: Entity

type Bin = ref object of Movable
  space: int

type LitterBag = ref object of Movable
  serves: int

type FoodBag = ref object of Movable
  serves: int

type Cat = ref object of Movable
  age: int
  love: int
  stress: float
  personality: CatPersonality

  flip: bool
  color: range[0..2]
  targetPos: Vec2i
  boredom: float

  wantsAttention: bool

  state: CatState

  route: seq[Tile]
  routeIndex: int
  routeTimeout: int

  needToSleep: float
  needEntertainment: float
  needSpace: float
  needToPoop: float
  needToWee: float
  needToEat: float
  needToDrink: float

  toiletTimeout: int
  eatTimeout: int

  usingObject: Entity

  socialised: int

type Box = ref object of Movable
  day: int
  hasCat: Cat
  money: int

type SprayCleaner = ref object of Movable
  sprays: int

type Courier = ref object of Entity
type GarbageTruck = ref object of Entity

type Player = ref object of Movable
  dir: int
  walking: bool
  holding: Entity

type Particle = object
  spr: int
  color: ColorId
  pos: Vec2f
  vel: Vec2f
  ttl: int
  text: string

type AdoptionReqs = tuple
  color: int
  personality: CatPersonality
  ageMin: int
  love: int

# GLOBALS

var hitFirstSmellThreshold = false
var hitSecondSmellThreshold = false
var gameOver = false
var adoptionList: seq[AdoptionReqs]
var adoptions = 0
var currentNoteText: string
var day = 0
var boxDay = 0
var bonus = 0
var cameraX = 0.0
var shopMode = false
var frame = 0
var gameTime = 0
var objects: seq[Entity]
var player: Player
var particles: seq[Particle]
var tilemap: Tilemap
var money: int
var spinMoneyTimer: int
var nCats: int = 0

var nausea: float
var houseSmell: float

var introTextIndex = 0
var introTextChar = 0
var titlePosition = -32.0

var noteTextIndex = -1
var noteTextChar = 0

var nextCharTimer = 0

# EARLY DEFS

proc hotspot(self: Entity): Vec2i
proc enterState(self: Cat, newState: CatState)

# INITIALISERS

proc newCat(pos: Vec2i): Cat =
  result = new(Cat)
  result.age = 0
  result.personality = rnd(CatPersonality.high.int+1).CatPersonality
  result.pos = pos
  result.color = rnd(3)
  result.targetPos = pos
  result.boredom = rnd(2.0)
  result.hitbox = (2,4,4,2)
  result.offset = vec2i(4, 6)
  result.state = Chill

  result.socialised = 0

  result.needToPoop = rnd(0.75)
  result.needToWee = rnd(0.75)

proc newCat(): Cat =
  result = new(Cat)
  result.age = 0
  result.personality = rnd(CatPersonality.high.int+1).CatPersonality
  result.color = rnd(3)
  result.hitbox = (2,4,4,2)
  result.offset = vec2i(4, 6)
  result.state = Sleep

  result.socialised = 0

proc newBox(pos: Vec2i): Box =
  result = new(Box)
  result.pos = pos
  result.hitbox = (1,1,6,4)
  result.offset = vec2i(4, 6)
  result.hasCat = newCat()
  result.day = boxDay
  result.money = boxDay * 10 + bonus
  boxDay += 1

proc newBin(pos: Vec2i): Bin =
  result = new(Bin)
  result.pos = pos
  result.hitbox = (1,2,6,5)
  result.offset = vec2i(4, 6)
  result.space = 4

proc newBowl(pos: Vec2i): Bowl =
  result = new(Bowl)
  result.pos = pos
  result.hitbox = (2,4,4,2)
  result.offset = vec2i(4, 5)

proc newFoodBag(pos: Vec2i): FoodBag =
  result = new(FoodBag)
  result.pos = pos
  result.serves = 5
  result.hitbox = (2,4,3,4)
  result.offset = vec2i(3, 6)

proc newLitterBag(pos: Vec2i): LitterBag =
  result = new(LitterBag)
  result.pos = pos
  result.serves = 5
  result.hitbox = (1,2,6,5)
  result.offset = vec2i(4, 6)

proc newLitterBox(pos: Vec2i): LitterBox =
  result = new(LitterBox)
  result.pos = pos
  result.poop = 0
  result.wee = 0
  result.hasLitter = false
  result.hitbox = (1,1,6,5)
  result.offset = vec2i(4, 6)

proc newGarbageTruck(pos: Vec2i): GarbageTruck =
  result = new(GarbageTruck)
  result.pos = pos
  result.hitbox = (8,8,1,1)
  result.offset = vec2i(8, 10)

proc newCourier(pos: Vec2i): Courier =
  result = new(Courier)
  result.pos = pos
  result.hitbox = (2,10,4,2)
  result.offset = vec2i(4, 10)

proc newPlayer(pos: Vec2i): Player =
  result = new(Player)
  result.pos = pos
  result.hitbox = (2,10,4,2)
  result.offset = vec2i(4, 10)
  result.dir = 3

proc newPoop(pos: Vec2i): Poop =
  result = new(Poop)
  result.pos = pos
  result.hitbox = (2,6,3,2)
  result.offset = vec2i(4, 7)

proc newWee(pos: Vec2i): Wee =
  result = new(Wee)
  result.pos = pos
  result.hitbox = (2,2,3,3)
  result.age = 0
  result.offset = vec2i(4,3)

proc newSprayCleaner(pos: Vec2i): SprayCleaner =
  result = new(SprayCleaner)
  result.pos = pos
  result.hitbox = (3,2,2,4)
  result.offset = vec2i(4,7)
  result.sprays = 5

# PROCS

proc line(a,b: Vec2f) =
  line(a.x, a.y, b.x, b.y)

proc clean(self: LitterBox): bool =
  return hasLitter and poop < 2 and wee < 2

proc spendMoney(amount: int): bool =
  if money >= amount:
    money -= amount
    spinMoneyTimer = 30
    synth(5, synP25, 2000, 4, -4)
    arp(5, 0xc000.uint16, 3)
    particles.add(Particle(spr: 73, text: "-$" & $amount, color: 14, pos: player.hotspot().vec2f + vec2f(0, -4), vel: vec2f(0, -0.1), ttl: 60))
    return true
  else:
    synth(5, synP25, 400, 4, -4)
    pitchbend(5, -2)
    spinMoneyTimer = 30
    return false

proc getMoney(amount: int) =
  if amount <= 0:
    return
  money += amount
  spinMoneyTimer = 30
  synth(5, synP25, 2000, 4, -4)
  arp(5, 0xc000.uint16, 3)
  particles.add(Particle(spr: 73, text: "+$" & $amount, color: 14, pos: player.hotspot().vec2f + vec2f(0, -4), vel: vec2f(0, -0.1), ttl: 60))

var contextName: string
var contextDesc: string

var contextX = 0.0
var contextY = screenHeight.float + 1.0

var showContext: bool

proc setContext(name, desc: string) =
  contextName = name
  contextDesc = desc
  showContext = contextName != ""

proc drawContext() =
  let targetContextY = (if showContext: 128 - 16 else: 129).float
  let targetContextX = (if player.pos.y >= screenHeight - 32 and player.pos.x >= cameraX + 64: 0 else: 64).float
  contextX = lerp(contextX, targetContextX, 0.1)
  contextY = lerp(contextY, targetContextY, 0.5)
  setColor(2)
  rectfill(contextX, contextY, contextX + 64, contextY + 16)
  setColor(10)
  rect(contextX + 1, contextY + 1, contextX + 63, contextY + 16 - 1)
  setColor(15)
  print(contextName, contextX + 3, contextY + 2)
  let text = contextDesc.splitLines()
  if text.len > 0:
    let line = text[((frame / 120) mod text.len)]
    print(line, contextX + 3, contextY + 8)

proc textBubble(text: string, x,y: int, color = 2) =
  let text = text.splitLines()
  var maxw = 0
  for line in text:
    let w = textWidth(line)
    if w > maxw:
      maxw = w

  let r = clamp(x - maxw div 2, 128 + 2, 256 - maxw - 4)
  # bg
  setColor(15)
  rectfill(r - 2 + 4, y - 2, r + maxw + 2 - 4, y + 7 * text.len + 2)

  circfill(r - 2 + 4, y + 4 - 2, 4)
  circfill(r - 2 + 4, y + 7 * text.len + 2 - 4, 4)

  circfill(r - 2 + maxw + 2, y + 4 - 2, 4)
  circfill(r - 2 + maxw + 2, y + 7 * text.len + 2 - 4, 4)

  rectfill(r - 2, y + 4, r + maxw + 4, y + 7 * text.len - 4)

  setColor(color)
  for i,line in text:
    printc(line, r + 2 + maxw div 2, y + i * 7)

proc hotspot(self: Entity): Vec2i =
  return self.pos + self.offset

proc dist(a,b: Vec2f): float =
  return (a - b).length

proc dist(a,b: Entity): float =
  return (a.hotspot.vec2f - b.hotspot.vec2f).length

proc objectAtTile(tx,ty: int): Entity =
  for obj in objects:
    if obj of Player:
      continue
    if obj of Cat:
      continue
    if obj.hotspot.x div 8 == tx and obj.hotspot.y div 8 == ty:
      return obj
  return nil

proc isSolid(t: uint8): bool =
  case t:
  of 50,53,55,52,68,83,25,27,125:
    return false
  else:
    return true

proc isPathable(t: uint8): bool =
  case t:
  of 50,55,48,52,68,83,25,27,125:
    return true
  else:
    return false

proc isSolid(tx,ty: int): bool =
  if tx < 0 or ty < 0 or tx > 15 or ty > 15:
    return false
  return isSolid(mget(tx,ty))

proc isPathable(tx,ty: int): bool =
  if tx < 0 or ty < 0 or tx > 15 or ty > 15:
    return false
  return isPathable(mget(tx,ty))

proc getTile(pos: Vec2i): Tile =
  let tx = pos.x div 8
  let ty = pos.y div 8
  return (x: tx, y: ty, t: mget(tx,ty))

proc cost(grid: Tilemap, a, b: Tile): int =
  if a.x == b.x or a.y == b.y:
    return 3
  else:
    return 4

proc heuristic(grid: Tilemap, next, goal: Tile): int =
  let dx = next.x - goal.x
  let dy = next.y - goal.y
  return dx*dx + dy*dy

iterator neighborsXY(node: Tile): Tile =
  let tx = node.x
  let ty = node.y

  yield (tx-1,ty,mget(tx-1,ty))
  yield (tx+1,ty,mget(tx+1,ty))
  yield (tx,ty-1,mget(tx,ty-1))
  yield (tx,ty+1,mget(tx,ty+1))

iterator neighbors(grid: Tilemap, node: Tile): Tile =
  let tx = node.x
  let ty = node.y

  if isPathable(tx-1,ty):
    yield (tx-1,ty,mget(tx-1,ty))
  if isPathable(tx+1,ty):
    yield (tx+1,ty,mget(tx+1,ty))
  if isPathable(tx,ty-1):
    yield (tx,ty-1,mget(tx,ty-1))
  if isPathable(tx,ty+1):
    yield (tx,ty+1,mget(tx,ty+1))

  if isPathable(tx-1,ty-1):
    yield (tx-1,ty-1,mget(tx-1,ty-1))

  if isPathable(tx-1,ty+1):
    yield (tx-1,ty+1,mget(tx-1,ty+1))

  if isPathable(tx+1,ty+1):
    yield (tx+1,ty+1,mget(tx+1,ty+1))

  if isPathable(tx+1,ty-1):
    yield (tx+1,ty-1,mget(tx+1,ty-1))

iterator adjacentTiles(pos: Vec2i): Tile =
  for n in neighborsXY((x: pos.x div 8, y: pos.y div 8, t: 0.uint8)):
    yield n

proc isTouchingType(x,y,w,h: int, check: proc(t: uint8): bool): bool =
  for i in x div 8..(x+w-1) div 8:
    for j in y div 8..(y+h-1) div 8:
      let t = mget(i,j)
      if check(t):
        return true
  return false

proc isSolid(self: Movable, ox,oy: int): bool =
  if isTouchingType(pos.x+hitbox.x+ox, pos.y+hitbox.y+oy, hitbox.w, hitbox.h, isSolid):
    return true
  return false

method getName(self: Entity): string {.base.} =
  return "?"

method getName(self: Cat): string =
  case self.personality:
  of Skittish:
    return "a skittish cat"
  of Outgoing:
    return "a social cat"
  of Dominant:
    return "a dominant cat"
  of Spontaneous:
    return "a zaney cat"
  of Friendly:
    return "a friendly cat"

method getName(self: Courier): string =
  return "a courier"

method getName(self: Box): string =
  return "a box"

method getName(self: Wee): string =
  return "urine stain"

method getName(self: LitterBox): string =
  return "litter box"

method getName(self: SprayCleaner): string =
  return "urine cleaner"

method getName(self: LitterBag): string =
  return "litter bag"

method getName(self: Poop): string =
  return "cat poop"

method getName(self: Bin): string =
  return "garbage bin"

method getName(self: FoodBag): string =
  return "bag of cat food"

method getName(self: Bowl): string =
  return "cat bowl"

proc love(self: Cat) =
  self.love += 1
  particles.add(Particle(spr: 43, pos: self.hotspot.vec2f, vel: vec2f(0, -0.1), ttl: 30))
  synth(6, synSqr, 1000, 2, -5)
  pitchbend(6, 1)
  arp(6, 0x2000.uint16, 2)

# METHODS

method getDescription(self: Entity): string {.base.} =
  return ""

method update(self: Entity, dt: float) {.base.} =
  discard

method drop(self: Entity) {.base.} =
  discard

method use(self: Entity) {.base.} =
  discard

method draw(self: Entity) {.base.} =
  setColor(8)
  circfill(pos.x, pos.y, 3)

method canGrab(self: Entity): bool {.base.} =
  return false

method onGrab(self: Entity) {.base.} =
  discard

proc moveX(self: Movable, amount: float, start: float) =
  var step = amount.int.sgn
  for i in start.int..<abs(amount.int):
    if not self.isSolid(step, 0):
      pos.x += step
    else:
      # hit something
      vel.x = 0
      rem.x = 0

proc moveY(self: Movable, amount: float, start: float) =
  var step = amount.int.sgn
  for i in start.int..<abs(amount.int):
    if not self.isSolid(0, step):
      pos.y += step
    else:
      # hit something
      vel.y = 0
      rem.y = 0

method update(self: Movable, dt: float) =
  if Entity(self) == player.holding:
    vel = vec2f(0,0)
    if player.dir == 0:
      pos = player.pos + player.offset - self.offset + vec2i(4, -2)
    if player.dir == 2:
      pos = player.pos + player.offset - self.offset + vec2i(-4, -2)
    if player.dir == 3:
      pos = player.pos + player.offset - self.offset + vec2i(0, -3)
    if player.dir == 1:
      pos = player.pos + player.offset - self.offset + vec2i(0, 1)
    return

  # check if on a solid tile, if so move them off it
  if self.isSolid(0,0):
    # find a free adjacent tile
    for i in 0..7:
      if not self.isSolid(-i,0):
        self.pos.x -= i
        break
      if not self.isSolid(i,0):
        self.pos.x += i
        break
      if not self.isSolid(0,-i):
        self.pos.y -= i
        break
      if not self.isSolid(0,+i):
        self.pos.y += i
        break

  rem.x += vel.x * dt
  let xAmount = flr(rem.x + 0.5)
  rem.x -= xAmount
  moveX(xAmount, 0.0)

  rem.y += vel.y * dt
  let yAmount = flr(rem.y + 0.5)
  rem.y -= yAmount
  moveY(yAmount, 0.0)

  vel *= (1.0 - friction)



method canGrab(self: Movable): bool =
  return true

method canGrab(self: Cat): bool =
  if usingObject != nil:
    return false
  return true

method onGrab(self: Cat) =
  if usingObject of Bowl:
    Bowl(usingObject).occupied = nil
  if usingObject of LitterBox:
    LitterBox(usingObject).occupied = nil
  usingObject = nil
  enterState(Wander)

method canGrab(self: LitterBox): bool =
  if occupied != nil:
    return false
  return true

method canGrab(self: Bowl): bool =
  if occupied != nil:
    return false
  return true

proc meetReq(self: Cat, req: AdoptionReqs): bool =
  return req.color == self.color and req.personality == self.personality and self.age >= req.ageMin and self.love div 2 >= req.love div 2

method use(self: Cat) =
  let tx = hotspot().x div 8
  let ty = hotspot().y div 8
  if (tx == 29 or tx == 30) and (ty == 10 or ty == 9):
    debug "used at adoption centre"
    for i, req in adoptionList:
      if self.meetReq(req):
        debug "accepted into adoption center"
        adoptionList.delete(i)
        toKill = true # =(
        getMoney(500)
        adoptions += 1
        currentNoteText = "CONGRATULATIONS\nYOU FOUND THIS CAT\nA FOREVER HOME!"
        noteTextChar = 0
        break

method use(self: Box) =
  if self.hasCat != nil:
    let cat = self.hasCat
    self.hasCat = nil
    cat.pos = self.pos
    cat.enterState(Wander)
    objects.add(cat)

    getMoney(self.money)
    self.money = 0

    if self.day < noteText.len:
      debug "opening note", self.day
      noteTextChar = 0
      currentNoteText = noteText[self.day]

      if self.day == 0:
        objects.add(newFoodBag(self.pos + vec2i(-4, -4)))
        objects.add(newBowl(self.pos + vec2i(4, 4)))

      if self.day == 1:
        objects.add(newLitterBox(self.pos + vec2i(-4, -4)))
        objects.add(newLitterBag(self.pos + vec2i(4, 4)))
    return
  particles.add(Particle(text: "empty", pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, -4.0), vel: vec2f(0, -0.1), ttl: 30))
  synth(5, synP25, 400, 4, -4)
  pitchbend(5, -2)


method use(self: SprayCleaner) =
  if sprays > 0:
    sprays -= 1
    particles.add(Particle(text: $sprays, pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, -4.0), vel: vec2f(0, -0.1), ttl: 30))
    synth(0, synNoise, 5000, 2, -4)
    pitchbend(0, 10)

    for obj in objects:
      if obj of Wee:
        let d = dist(self, obj)
        if d < 8:
          let wee = Wee(obj)
          if wee.age < 60 * 30:
            wee.toKill = true
    return
  else:
    for obj in objects:
      if obj of Bin:
        let bin = Bin(obj)
        if bin.space > 0:
          let d = dist(self, bin)
          if d < 8:
            player.holding = nil
            self.toKill = true
            bin.space -= 1
            return

  if sprays == 0:
    particles.add(Particle(text: "empty", pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, -4.0), vel: vec2f(0, -0.1), ttl: 30))
    synth(5, synP25, 400, 4, -4)
    pitchbend(5, -2)

method draw(self: Box) =
  if hasCat != nil:
    spr(92, pos.x, pos.y)
  else:
    spr(72, pos.x, pos.y)

method draw(self: Poop) =
  spr(5, pos.x, pos.y)

method draw(self: SprayCleaner) =
  spr(39, pos.x, pos.y)

method draw(self: Bin) =
  if space > 0:
    spr(17, pos.x, pos.y)
  else:
    spr(18, pos.x, pos.y)

method draw(self: Bowl) =
  spr(if foodServes > 0: 33 elif waterServes > 0: 34 else: 35, pos.x, pos.y)

method draw(self: GarbageTruck) =
  if gameTime mod 10 < 5:
    spr(96, pos.x, pos.y, 3, 3)
  else:
    spr(99, pos.x, pos.y, 3, 3)

method draw(self: LitterBox) =
  if not hasLitter:
    spr(24, pos.x, pos.y)
  else:
    if wee > 2:
      pal(13, 14)
    spr(19 + min(poop,3), pos.x, pos.y)
    pal()

method draw(self: LitterBag) =
  spr(38, pos.x, pos.y)

method draw(self: FoodBag) =
  spr(36, pos.x, pos.y)

method getDescription(self: Bin): string =
  if space <= 0:
    return "FULL"
  return "space: " & $self.space

method getDescription(self: Cat): string =
  return $(self.age + 1) & " days " & (if stress > 1.0: repeat('&', (stress / 2.0).int) else: repeat('#', love div 2))

method getDescription(self: Box): string =
  if hasCat != nil:
    return "it's meowing!\nX to open"
  else:
    return "it's empty\nZ to drop"

var meowTimeout = 0

proc meow(self: Cat) =
  if shopMode:
    return
  if meowTimeout <= 0:
    synth(1, synP12, 1046 + rnd(100.0) - 50.0, 4, -4)
    pitchbend(1, 2)
    meowTimeout = 10

method getDescription(self: LitterBag): string =
  return "serves: " & $self.serves

method getDescription(self: FoodBag): string =
  return "serves: " & $self.serves & "\nX to fill bowl"

method getDescription(self: Bowl): string =
  return "serves: " & $self.foodServes

method getDescription(self: SprayCleaner): string =
  if self.sprays == 0:
    return "EMPTY!"
  return "sprays: " & $self.sprays

method update(self: Box, dt: float) =
  if hasCat != nil:
    if gameTime mod 10 == 0 and rnd(10) == 0:
      particles.add(Particle(text: "!", color: 6, pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, -4.0), vel: vec2f(0, -0.1), ttl: 30))
      synth(2, synP12, 500 + rnd(100.0) - 50.0, 2, -4)
      pitchbend(2, 2)


  procCall update(Movable(self), dt)

method use(self: Bowl) =
  # check if it's near a bin, if so, empty it
  if self.foodServes > 0 or self.waterServes > 0:
    for obj in objects:
      if obj of Bin:
        let bin = Bin(obj)
        if bin.space > 0:
          if dist(bin,self) < 8:
            self.foodServes = 0
            self.waterServes = 0
            bin.space -= 1

method use(self: LitterBox) =
  # check if it's near a bin, if so, empty it
  if self.hasLitter:
    for obj in objects:
      if obj of Bin:
        let bin = Bin(obj)
        if bin.space > 0:
          if dist(bin,self) < 8:
            self.poop = 0
            self.wee = 0
            self.hasLitter = false
            bin.space -= 1

method use(self: Poop) =
  for obj in objects:
    if obj of Bin:
      let bin = Bin(obj)
      if bin.space > 0:
        if dist(obj,self) < 8:
          self.toKill = true
          player.holding = nil
          bin.space -= 1
          return
    if obj of LitterBox and LitterBox(obj).hasLitter:
      if dist(obj,self) < 8:
        let box = LitterBox(obj)
        box.poop += 1
        self.toKill = true
        player.holding = nil
        return

method use(self: FoodBag) =
  if serves > 0:
    for obj in objects:
      if obj of Bowl and Bowl(obj).foodServes < 4:
        if dist(obj,self) < 8:
          Bowl(obj).foodServes += 4
          serves -= 1
          particles.add(Particle(text: $serves, pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, -4.0), vel: vec2f(0, -0.1), ttl: 30))
          synth(0, synNoise, 1000, 2, -2)
          pitchbend(0, -1)
          return
  else:
    for obj in objects:
      if obj of Bin:
        let bin = Bin(obj)
        if bin.space > 0:
          if dist(obj,self) < 8:
            self.toKill = true
            player.holding = nil
            bin.space -= 1
            return
  if serves == 0:
    particles.add(Particle(text: "empty", pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, -4.0), vel: vec2f(0, -0.1), ttl: 30))
    synth(5, synP25, 400, 4, -4)
    pitchbend(5, -2)



method use(self: LitterBag) =
  # check if it's near a bin, if so, empty it
  if serves > 0:
    for obj in objects:
      if obj of LitterBox and not LitterBox(obj).hasLitter:
        if dist(obj,self) < 8:
          LitterBox(obj).hasLitter = true
          serves -= 1
          particles.add(Particle(text: $serves, pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, -4.0), vel: vec2f(0, -0.1), ttl: 30))
          synth(0, synNoise, 1000, 2, -2)
          pitchbend(0, -1)
          return
  else:
    for obj in objects:
      if obj of Bin:
        let bin = Bin(obj)
        if bin.space > 0:
          if dist(bin,self) < 8:
            self.toKill = true
            player.holding = nil
            bin.space -= 1
            return

  if serves == 0:
    particles.add(Particle(text: "empty", pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, -4.0), vel: vec2f(0, -0.1), ttl: 30))
    synth(5, synP25, 400, 4, -4)
    pitchbend(5, -2)


method update(self: Courier, dt: float) =
  if frame mod 6 == 0:
    pos.x += 1

    if pos.x == 3*8 + 4:
      if objectAtTile(3,13) == nil:
        let box = newBox(vec2i(3*8, 13*8))
        synth(0, synSqr, 100.0, 4, -2)
        pitchbend(0, -10)
        objects.add(box)
        bonus += 1
      else:
        bonus = 0

  if pos.x > cameraX + screenWidth:
    toKill = true

method update(self: GarbageTruck, dt: float) =
  if gameTime mod 5 == 0:
    pos.x += 1

  if pos.x mod 8 == 4:
    for obj in objects:
      if obj == player.holding:
        continue
      if obj.pos.x div 8 == pos.x div 8 and pos.y div 8 >= 13:
        if obj of Bin:
          Bin(obj).space = 4
        if obj of Box and Box(obj).hasCat == nil:
          obj.toKill = true

  if pos.x > 255:
    toKill = true

method update(self: Wee, dt: float) =
  age += 1

  if age < 60 * 30:
    if rnd(120) == 0:
      particles.add(Particle(spr: 8, pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, 0), vel: vec2f(0, -0.1), ttl: 30))

method draw(self: Wee) =
  if age < 60 * 30:
    spr(6, pos.x, pos.y)
  else:
    spr(9, pos.x, pos.y)

method draw(self: Courier) =
  if gameTime mod 10 < 5:
    spr(29, pos.x, pos.y, 1, 2)
  else:
    spr(30, pos.x, pos.y, 1, 2)

method draw(self: Player) =
  if dir == 0: # right
    if walking and gameTime mod 10 < 5:
      spr(62, pos.x, pos.y, 1, 2)
    else:
      spr(61, pos.x, pos.y, 1, 2)
  elif dir == 1: # down
    if walking:
      if gameTime mod 10 < 5:
        spr(63, pos.x, pos.y, 1, 2)
      else:
        spr(63, pos.x, pos.y, 1, 2, true)
    else:
      spr(16, pos.x, pos.y, 1, 2)
  elif dir == 2: # left
    if walking and gameTime mod 10 < 5:
      spr(62, pos.x, pos.y, 1, 2, true)
    else:
      spr(61, pos.x, pos.y, 1, 2, true)
  elif dir == 3: # up
    if walking:
      if gameTime mod 10 < 5:
        spr(12, pos.x, pos.y, 1, 2)
      else:
        spr(12, pos.x, pos.y, 1, 2, true)
    else:
      spr(31, pos.x, pos.y, 1, 2)

method update(self: Player, dt: float) =
  procCall update(Movable(self), dt)

method update(self: Poop, dt: float) =
  procCall update(Movable(self), dt)

  if rnd(120) == 0:
    particles.add(Particle(spr: 7, pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, 0), vel: vec2f(0, -0.1), ttl: 30))

method update(self: LitterBox, dt: float) =
  if poop > 0:
    if rnd(600 div poop) == 0:
      particles.add(Particle(spr: 7, pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, 0), vel: vec2f(0, -0.1), ttl: 30))

  if wee > 0:
    if rnd(600 div wee) == 0:
      particles.add(Particle(spr: 8, pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, 0), vel: vec2f(0, -0.1), ttl: 30))

  procCall update(Movable(self), dt)

proc snap(pos: Vec2i): Vec2i =
  return vec2i((pos.x div 8) * 8, (pos.y div 8) * 8)

proc pathTo(self: Cat, goal: Vec2i) =
  targetPos = goal
  # try and find path to targetPos
  let start = getTile(self.hotspot + vec2i(0,-1))
  let goal = getTile(goal)

  route = newSeq[Tile]()
  routeIndex = 0
  for point in path[Tilemap, Tile, float](tilemap, start, goal):
    route.add(point)
  if route.len > 0:
    routeTimeout = 60 * 5
  else:
    routeTimeout = 60


proc enterState(self: Cat, newState: CatState) =
  case newState:
  of Chill:
    route = @[]
    #particles.add(Particle(text: "chill", pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, 0), vel: vec2f(0, -0.1), ttl: 60))
  of Sleep:
    route = @[]
    #particles.add(Particle(text: "sleep", pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, 0), vel: vec2f(0, -0.1), ttl: 60))
  of GoToToilet:
    toiletTimeout = 120
    route = @[]
    #particles.add(Particle(text: "toilet", pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, 0), vel: vec2f(0, -0.1), ttl: 60))
  of GoToEat:
    eatTimeout = 300
    route = @[]
    #particles.add(Particle(text: "eat", pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, 0), vel: vec2f(0, -0.1), ttl: 60))
  of Wander:
    route = @[]
    #particles.add(Particle(text: "wander", pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, 0), vel: vec2f(0, -0.1), ttl: 60))
  of Hyper:
    route = @[]
    #particles.add(Particle(text: "hyper", pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, 0), vel: vec2f(0, -0.1), ttl: 60))
  else:
    discard
  state = newState

method drop(self: Cat) =
  enterState(Wander)

method update(self: Cat, dt: float) =
  if houseSmell < 10.0:
    stress *= 0.95

  if wantsAttention:
    stress += 1.0

    if rnd(60) == 0:
      particles.add(Particle(text: "!", color: 6, pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, 0), vel: vec2f(0, -0.1), ttl: 30))
      meow()

  stress = clamp(stress, 0.0, 100.0)
  love = clamp(love, 0, 10)

  needToPoop += dt * 0.01 * rnd(1.0)
  needToWee += dt * 0.0125 * rnd(1.0)
  needToEat += dt * 0.03 * rnd(1.0)

  if state != Sleep:
    needToSleep += dt * 0.005 * rnd(1.0)

  for obj in objects:
    if obj of Cat and obj != self:
      let d = dist(obj, self)
      if d < 4 and d > 0:
        # too close to another cat, move away
        let dir = (self.hotspot().vec2f - obj.hotspot().vec2f).normalized
        self.vel += dir * 4.0


  case state:
  of Chill:
    boredom += dt * rnd(1.0)
    if needToPoop > 0.75 or needToWee > 0.75:
      enterState(GoToToilet)
    if needToEat > 0.75:
      enterState(GoToEat)
    if needToSleep > 0.75:
      enterState(Sleep)
    if boredom > 2.0:
      boredom = 0
      enterState(Wander)

  of Wander:
    boredom += dt * rnd(1.0) * 0.5
    if route.len == 0:
      # pick a random spot to wander to
      while true:
        let tx = 1 + rnd(14)
        let ty = 1 + rnd(11)
        if not isSolid(tx,ty):
          pathTo(vec2i(tx*8+4,ty*8+4))
          break
    if boredom > 2.0:
      boredom = 0
      enterState(Chill)

  of Hyper:
    needToSleep += dt * rnd(1.0) * 0.5
    if route.len == 0:
      # pick a random spot to wander to
      while true:
        let tx = 1 + rnd(14)
        let ty = 1 + rnd(11)
        if not isSolid(tx,ty):
          pathTo(vec2i(tx*8+4,ty*8+4))
          break
    if needToSleep > 1.0:
      enterState(Sleep)

  of Sleep:
    needToSleep -= dt * 0.05
    if gameTime mod 20 == 0:
      particles.add(Particle(text: "Z", pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, 0), vel: vec2f(0, -0.1), ttl: 10))

    if needToSleep <= 0.0:
      needToSleep = 0
      enterState(Chill)
    elif needToSleep < 0.25:
      if rnd(5000) == 0:
        needToSleep = 0
        enterState(Wander)

  of GoToEat:
    if usingObject != nil:
      let bowl = Bowl(usingObject)
      bowl.occupied = self
      if bowl.foodServes > 0:
        if gameTime mod 30 == 0:
          particles.add(Particle(text: "nom", pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, -4.0), vel: vec2f(0, -0.1), ttl: 30))
        eatTimeout -= 1
        needToPoop += dt * 0.01 * rnd(1.0)
        if eatTimeout <= 0:
          bowl.foodServes -= 1
          bowl.occupied = nil
          usingObject = nil
          needToEat = 0
          love()
          enterState(Wander)

    elif route.len == 0:
      # find a free bowl
      for obj in objects:
        if obj of Bowl:
          let bowl = Bowl(obj)
          if bowl.occupied == nil and bowl.foodServes > 0:
            pathTo(bowl.hotspot)
            break
      if route.len == 0:
        for obj in objects:
          if obj of Bowl:
            let bowl = Bowl(obj)
            pathTo(bowl.hotspot)
            break
    else:
      for obj in objects:
        if obj of Bowl:
          let d = dist(obj, self)
          if d < 8:
            let bowl = Bowl(obj)
            if bowl.occupied == nil and bowl.foodServes > 0:
              bowl.occupied = self
              self.usingObject = bowl
              self.pos.y = bowl.pos.y + 2
              self.pos.x = bowl.pos.x
              wantsAttention = false
              route = @[]
              break
      if self.usingObject == nil:
        wantsAttention = true


  of GoToToilet:
    if usingObject != nil:
      if usingObject of LitterBox:
        let box = LitterBox(usingObject)
        box.occupied = self
        toiletTimeout -= 1


        if toiletTimeout <= 0:
          box.occupied = nil
          usingObject = nil
          if box.clean:
            love()

          if needToPoop > 0.5:
            needToPoop = 0
            box.poop += 1
          if needToWee > 0.5:
            needToWee = 0
            box.wee += 1
          enterState(Wander)
      else:
        if usingObject of Bowl:
          Bowl(usingObject).occupied = nil
        usingObject = nil

    elif route.len == 0:
      var boxes = newSeq[LitterBox]()
      for obj in objects:
        if obj of LitterBox:
          let box = LitterBox(obj)
          if box.hasLitter:
            if box.poop < 5 and box.wee < 5:
              boxes.add(LitterBox(obj))

      boxes = boxes.sortedByIt(it.poop)
      while boxes.len > 0:
        pathTo(boxes[0].hotspot + vec2i(0, 0))
        if route.len > 0:
          break
        else:
          boxes.delete(0)

    # if near a box, use it
    else:
      for obj in objects:
        if obj of LitterBox:
          let box = LitterBox(obj)
          if box.occupied == nil and box.hasLitter and box.poop < 5 and box.wee < 5:
            let d = dist(obj,self)
            if d < 8:
              usingObject = box
              box.occupied = self
              self.pos.y = box.pos.y + 2
              self.pos.x = box.pos.x
              route = @[]
              break

  if route.len > 0:
    if routeIndex > route.high:
      route = @[]

    else:
      # try and find a new path if we get stuck
      routeTimeout -= 1
      if routeTimeout <= 0:
        pathTo(targetPos)

  if usingObject == nil or not (usingObject of LitterBox):
    # have to go right now
    if needToPoop > 1.0:
      objects.add(newPoop(pos))
      needToPoop = 0

    if needToWee > 1.0:
      objects.add(newWee(pos))
      needToWee = 0

  # follow route
  if route.len > 0:
    let diff = (vec2f(route[routeIndex].x * 8 + 4, route[routeIndex].y * 8 + 4) - self.hotspot.vec2f)
    let d = diff.length

    if state == Wander:
      if mget(route[routeIndex].x, route[routeIndex].y) == 48:
        wantsAttention = true
      else:
        if wantsAttention:
          love()
        wantsAttention = false

    if d < 0.5:
      routeIndex += 1
      if routeIndex > route.high:
        route = @[]
        routeIndex = 0

    else:
      vel += diff.normalized() * (if state == Wander: 5.0 elif state == Hyper: 15.0 else: 10.0)

  if vel.x > 0.1:
    flip = true
  elif vel.x < -0.1:
    flip = false

  procCall update(Movable(self), dt)

method draw(self: Cat) =
  case color:
  of 0:
    pal(1, 9)
    pal(2, 0)
  of 1:
    pal(1, 15)
    pal(2, 0)
  of 2:
    pal(1, 0)
    pal(2, 14)

  case state:
  of Sleep:
    spr(3, pos.x, pos.y, 1,1, flip)
  of Chill:
    spr(2, pos.x, pos.y, 1,1, flip)
  else:
    if stress > 5:
      spr(if vel.length > 0.5: (if gameTime mod 30 < 15: 4 else: 145) else: 4, pos.x, pos.y, 1, 1, flip)
    else:
      spr(if vel.length > 0.5: (if gameTime mod 30 < 15: 1 else: 144) else: 0, pos.x, pos.y, 1, 1, flip)
  pal()

  when false:
    if route != nil:
      setColor(6)
      for i in (routeIndex+1)..<route.len:
        line(route[i-1].x * 8 + 4, route[i-1].y * 8 + 4, route[i].x * 8 + 4, route[i].y * 8 + 4)

      setColor(14)
      circ(targetPos.x, targetPos.y, 4)

      setColor(14)
      line(self.hotspot.vec2f, self.hotspot.vec2f + vel * 2)

    if usingObject != nil:
      setColor(14)
      line(self.hotspot.x, self.hotspot.y, usingObject.hotspot.x, usingObject.hotspot.y)

# GAME

proc gameInit() =
  loadPaletteFromGPL("palette.gpl")

  loadSpritesheet(0, "spritesheet.png")
  setSpritesheet(0)

  loadFont(0, "font.png")
  setFont(0)

  loadMusic(0, "music/meow.ogg")

  loadMap(0, "map.json")
  setMap(0)

  money = 500

  adoptionList = newSeq[AdoptionReqs]()

  for i in 0..rnd(3):
    var req: AdoptionReqs
    req.color = rnd(3)
    req.personality = rnd(CatPersonality.high.int+1).CatPersonality
    req.ageMin = 5 + rnd(5)
    req.love = 5 + rnd(5)
    adoptionList.add(req)
  while adoptionList.len > 5:
    adoptionList.delete(0)

  objects = newSeq[Entity]()

  for y in 0..15:
    for x in 0..31:
      let t = mget(x,y)
      if t == 17:
        objects.add(newBin(vec2i(x*8, y*8)))
        mset(x,y,50)
      elif t == 24:
        objects.add(newLitterBox(vec2i(x*8, y*8)))
        mset(x,y,50)
      elif t == 38:
        objects.add(newLitterBag(vec2i(x*8, y*8)))
        mset(x,y,50)
      elif t == 39:
        objects.add(newSprayCleaner(vec2i(x*8, y*8)))
        mset(x,y,50)
      elif t == 16:
        debug "found player"
        player = newPlayer(vec2i(x*8, y*8 - 4))
        objects.add(player)
        mset(x,y,50)
      elif t == 0:
        objects.add(newCat(vec2i(x*8, y*8)))
        mset(x,y,50)
      elif t == 35:
        objects.add(newBowl(vec2i(x*8, y*8)))
        mset(x,y,50)
      elif t == 36:
        objects.add(newFoodBag(vec2i(x*8, y*8)))
        mset(x,y,50)

  if player == nil:
    raise newException(Exception, "No player")

proc gameUpdate(dt: float32) =
  if meowTimeout > 0:
    meowTimeout -= 1
  frame += 1

  if introTextIndex < introText.high:
    nextCharTimer -= 1
    if nextCharTimer <= 0:
      if introTextChar < introText[introTextIndex].high:
        introTextChar += 1
        let nextChar = introText[introTextIndex][introTextChar]
        nextCharTimer = case nextChar:
        of ' ': 6
        of '\r': 30
        of '.': 30
        of ',': 15
        else: 4
        if btn(pcA):
          nextCharTimer = nextCharTimer div 2

        if nextChar notin [' ', '\r', '.', ',']:
          synth(4, rnd([synSqr,synP12,synP25]), 400.0 + rnd(100.0), 4, -2)
          arp(4, rnd([0x2300, 0x3400, 0x7400, 0x1200]).uint16, 1)

    if btnp(pcStart):
      introTextIndex = introText.high
      let c = newCourier(vec2i(-8, 14*8 - 4))
      objects.add(c)
      music(0, 15)
      return

    if introTextChar == introText[introTextIndex].high and btnp(pcA):
      introTextIndex += 1
      introTextChar = 0
      nextCharTimer = 0
      if introTextIndex == introText.high:
        let c = newCourier(vec2i(-8, 14*8 - 4))
        objects.add(c)
        music(0, 15)

    return

  if currentNoteText != "":
    nextCharTimer -= 1
    if nextCharTimer <= 0:
      if noteTextChar < currentNoteText.high:
        noteTextChar += 1

        let nextChar = currentNoteText[noteTextChar]
        nextCharTimer = case nextChar:
        of ' ': 6
        of '\r': 30
        of '.': 30
        of ',': 15
        else: 4

        if btn(pcA):
          nextCharTimer = nextCharTimer div 2

        if nextChar notin [' ', '\r', '.', ',']:
          synth(4, rnd([synSqr,synP12,synP25]), 400.0 + rnd(100.0), 4, -2)
          arp(4, rnd([0x2300, 0x3400, 0x7400, 0x1200]).uint16, 1)

    if btnp(pcStart):
      currentNoteText = ""
      return
    if noteTextChar == currentNoteText.high and btnp(pcA):
      currentNoteText = ""
      noteTextChar = 0
    return

  gameTime += 1

  if not shopMode and player.pos.x >= 16 * 8:
    #if day >= 2:
    shopMode = true
  if shopMode and player.pos.x < 16 * 8:
    shopMode = false

  if shopMode:
    cameraX = lerp(cameraX, 128.0, 0.1)
    if cameraX > 127.9:
      cameraX = 128
  else:
    cameraX = lerp(cameraX, 0, 0.1)
    if cameraX < 0.1:
      cameraX = 0

  if gameTime mod (30 * 60) == 0:
    day += 1

    for obj in objects:
      if obj of Cat:
        Cat(obj).age += 1

    let c = newCourier(vec2i(-8, 14*8 - 4))
    objects.add(c)

    if day mod 7 == 0:
      # new adoptions
      for i in 0..rnd(3):
        var req: AdoptionReqs
        req.color = rnd(3)
        req.personality = rnd(CatPersonality.high.int+1).CatPersonality
        req.ageMin = 10 + rnd(5)
        req.love = 5 + rnd(5)
        adoptionList.add(req)
      while adoptionList.len > 5:
        adoptionList.delete(0)

    if day mod 7 == 4:
      objects.add(newGarbageTruck(vec2i(-32, 14*8)))

  if spinMoneyTimer > 0:
    spinMoneyTimer -= 1

  # input for player
  player.walking = false
  if btn(pcLeft):
    player.vel.x -= playerAccel
    player.dir = 2
    player.walking = true
  if btn(pcRight):
    player.vel.x += playerAccel
    player.dir = 0
    player.walking = true
  if btn(pcUp):
    player.vel.y -= playerAccel
    player.dir = 3
    player.walking = true
  if btn(pcDown):
    player.vel.y += playerAccel
    player.dir = 1
    player.walking = true

  if btnp(pcB):
    # USE button [X]
    if player.holding == nil:
      # check if adjacent to door
      for tile in adjacentTiles(player.pos + player.offset):
        if tile.t == 48:
          mset(tile.x, tile.y, 55)
          synth(0, synNoise, 1000, 2, -2)
          pitchbend(0, -1)
          break
        elif tile.t == 55:
          synth(0, synNoise, 1000, 2, -2)
          pitchbend(0, 1)
          mset(tile.x, tile.y, 48)
          break
        elif tile.t == 105:
          synth(0, synSqr, 500, 2, -7)
          arp(0, rnd(0xffff).uint16, 3)
          if boxDay == 0:
            currentNoteText = "I SHOULD GO CHECK WHAT'S\nAT THE DOOR..."
          else:
            currentNoteText = "IT SEEMS TO HAVE A VIRUS =("
          noteTextChar = 0
          break

    else:
      player.holding.use()

  if btnp(pcA):
    if player.holding == nil:
      # search for the nearest object and hold it
      var nearestDist = Inf
      var nearestObj: Entity
      for obj in objects:
        if obj.canGrab():
          if obj == player:
            continue
          if not (obj of Movable):
            continue
          let d = dist(obj,player)
          if d > 8:
            continue
          if d < nearestDist:
            nearestDist = d
            nearestObj = obj
      if nearestObj != nil and nearestObj.canGrab():
        nearestObj.onGrab()
        player.holding = nearestObj
        synth(0, synSqr, 100.0, 4, -2)
        pitchbend(0, 10)
    else:
      #player.holding.pos = snap(player.hotspot)
      player.holding.pos.y = player.hotspot.y - player.holding.offset.y
      player.holding.drop()
      player.holding = nil
      synth(0, synSqr, 100.0, 4, -2)
      pitchbend(0, -10)
      #  synth(0, synNoise, 1000.0, 2, -3)
      #  pitchbend(0, -1)


  for i in 0..<objects.len:
    objects[i].update(dt)

  for p in mitems(particles):
    p.ttl -= 1
    p.pos += p.vel

  particles = particles.filterIt(it.ttl > 0)

  objects = objects.filterIt(not it.toKill)

  nausea *= 0.9

  houseSmell = 0

  nCats = 0

  for obj in objects:
    if obj of Cat:
      nCats += 1
    if obj of Poop:
      houseSmell += 5.0
    if obj of Wee:
      if Wee(obj).age > 60:
        houseSmell += 1.0
      else:
        houseSmell += 2.0
    if obj of LitterBox:
      let box = LitterBox(obj)
      houseSmell += box.poop.float * 1.0
      houseSmell += box.wee.float * 0.5

  if not hitFirstSmellThreshold and houseSmell > 10:
    if not shopMode:
      currentNoteText = "THE HOUSE IS GETTING\nREALLY SMELLY!\nCLEAN IT UP!"
      noteTextChar = 0
      hitFirstSmellThreshold = true

  if not hitSecondSmellThreshold and houseSmell > 20:
    if not shopMode:
      currentNoteText = "YOU NEED TO CLEAN\nTHIS PLACE UP\nASAP!!"
      noteTextChar = 0
      hitSecondSmellThreshold = true

  if houseSmell > 30:
    currentNoteText = "YOUR HOUSE HAS BEEN\nSHUT DOWN BY THE COUNCIL!\nTHE END."
    noteTextChar = 0
    gameOver = true

  for p in particles:
    if p.spr == 7 or p.spr == 8:
      let d = dist(p.pos + vec2f(4,4), player.hotspot().vec2f)
      if d < 8:
        nausea += 0.5

proc glitchBlur*(x,y,w,h: Pint, offset: Pint) =
  # warp the screen memory
  var tmp = newSeq[uint8](w)
  for yi in y..h:
    # left side
    copyPixelsToMem(x, yi, tmp)
    copyMemToScreen(x+rnd(offset*2)-offset, yi, tmp)

proc sortProc(a,b: Entity): int =
  if player.holding == a:
    return 1
  if player.holding == b:
    return -1
  return (a.pos.y + a.hitbox.y + a.hitbox.h) - (b.pos.y + b.hitbox.y + b.hitbox.h)

proc shadowMode() =
  for i in 1..15:
    pal(i,0)

proc gameDraw() =

  if gameOver:
    setCamera()
    setColor(0)
    rectfill(0,0,screenWidth, screenHeight)

    setColor(10)
    printc("THE END", screenWidth div 2, screenHeight div 2)

    return

  setColor(3)
  rectfill(0,0,256, screenHeight)

  setCamera(cameraX,0)
  mapDraw(0,0,32,16,0,0)

  if day >= 2:
    setColor(3)
    printr("SHOPS ->", 120, 114)

  setColor(3)
  print("<- HOME", 130, 114)

  objects.sort(sortProc)

  for obj in objects:
    obj.draw()
    setColor(6)
    #rect(obj.pos.x + obj.hitbox.x, obj.pos.y + obj.hitbox.y, obj.pos.x + obj.hitbox.x + obj.hitbox.w - 1, obj.pos.y + obj.hitbox.y + obj.hitbox.h - 1)

  for p in particles:
    if p.text != "" and p.spr != 0:
      let tw = textWidth(p.text) div 2
      spr(p.spr, p.pos.x - tw - 4, p.pos.y - 7)
      setColor(p.color)
      printc(p.text, p.pos.x, p.pos.y - 4)
    elif p.text != "":
      setColor(p.color)
      printc(p.text, p.pos.x, p.pos.y - 4)
    else:
      spr(p.spr, p.pos.x - 4, p.pos.y - 7)

  setColor(0)
  rectfill(1,1,1+30,6)
  setColor(1)
  rectfill(1,1,1+houseSmell.int,6)

  if houseSmell > 20:
    setColor(9)
    print("EWWWW!", 3, 1)
  elif houseSmell > 10:
    setColor(7)
    print("SMELLY!", 3, 1)
  elif houseSmell > 5:
    setColor(7)
    print("MEH!", 3, 1)
  else:
    setColor(7)
    print("CLEAN", 3, 1)


  setColor(0)
  print($adoptions & "/" & $nCats & " CATS", 34, 1)

  if gameTime mod 20 < 10 and (gameTime / 30 / 60).float mod 1.0 < 0.05:
    setColor(15)
  else:
    setColor(11)
  print(daysOfWeek[day mod 7], 82, 1)
  hline(82, 7, 82.0 + ((gameTime / 30 / 60).float mod 1.0) * 11)

  if shopMode:
    if player.hotspot.y div 8 == 10:
      let tx = player.hotspot.x div 8

      if tx == 29:
        textBubble("WELCOME TO\nTHE CAT ADOPTION CENTRE", screenWidth + screenWidth div 2, 2 * 8)
        var y = 5 * 8 + 4
        if adoptionList.len == 0:
          textBubble("THERE IS NO ONE\nLOOKING TO ADOPT\nCURRENTLY", screenWidth + screenWidth div 2, y)
        else:
          textBubble("CURRENTLY LOOKING FOR:", screenWidth + screenWidth div 2, y)
          y += 8
          for req in adoptionList:
            textBubble(repeat('#', req.love div 2) & " " & $(req.color.CatColor) & " " & $req.personality & " " & $req.ageMin & "+ days", screenWidth + screenWidth div 2, y, if player.holding != nil and player.holding of Cat and Cat(player.holding).meetReq(req): 6 else: 2)
            y += 8

      if tx == 18 or tx == 23 or tx == 26:
        if player.holding == nil:
          textBubble("STAND IN FRONT OF THE\NITEM YOU WANT TO BUY", tx * 8, 4 * 8)
        else:
          textBubble("YOU CAN'T CARRY ANY MORE", tx * 8, 4 * 8)

      if player.holding == nil:
        if tx == 17:
          textBubble("URINE CLEANER\n$200 [X]", 17 * 8, 4 * 8)
          if player.holding == nil and btnp(pcB):
            if spendMoney(200):
              player.holding = newSprayCleaner(player.pos)
              objects.add(player.holding)

        if tx == 19:
          textBubble("GARBAGE BIN\n$250 [X]", tx * 8, 4 * 8)
          if player.holding == nil and btnp(pcB):
            if spendMoney(250):
              player.holding = newBin(player.pos)
              objects.add(player.holding)

        if tx == 21:
          textBubble("CAT BOWL\n$200 [X]", tx * 8, 4 * 8)
          if player.holding == nil and btnp(pcB):
            if spendMoney(200):
              player.holding = newBowl(player.pos)
              objects.add(player.holding)

        if tx == 22:
          textBubble("CAT FOOD\n$100 [X]", tx * 8, 4 * 8)
          if player.holding == nil and btnp(pcB):
            if spendMoney(100):
              player.holding = newFoodBag(player.pos)
              objects.add(player.holding)

        if tx == 25:
          textBubble("KITTY LITTER\n$100 [X]", tx * 8, 4 * 8)
          if player.holding == nil and btnp(pcB):
            if spendMoney(100):
              player.holding = newLitterBag(player.pos)
              objects.add(player.holding)

        if tx == 27:
          textBubble("LITTER BOX\n$200 [X]", tx * 8, 4 * 8)
          if player.holding == nil and btnp(pcB):
            if spendMoney(200):
              player.holding = newLitterBox(player.pos)
              objects.add(player.holding)

  setCamera()

  setColor(14 + (if spinMoneyTimer > 0 and  frame mod 10 < 5: 1 else: 0))
  printr($money, screenWidth - 8, 1)
  spr(73 + (if spinMoneyTimer > 0: (frame div 10) mod 4 else: 0), screenWidth - 8, 0)

  # CONTEXT INFO

  showContext = false

  if player.holding != nil:
    setContext(player.holding.getName, player.holding.getDescription)
  else:
    # find nearest object
    var nearestObj: Entity = nil
    var nearestDist = Inf
    for obj in objects:
      if obj != player:
        let d = dist(obj,player).float
        if d < nearestDist and d < 8:
          nearestDist = d
          nearestObj = obj

    if nearestObj != nil:
      setContext(nearestObj.getName, if nearestObj.canGrab(): "Z to pick up" else: "")
    else:
      for tile in adjacentTiles(player.pos + player.offset):
        if tile.t == 48:
          setContext("door", "X to open")
          break
        if tile.t == 55:
          setContext("door", "X to close")
          break
        if tile.t == 105:
          setContext("computer", "X to use")
          break

  drawContext()

  for i in 0..<min(nausea.int,20):
    glitchBlur(0,0,screenWidth,screenHeight,1)

  if gameTime < 100:
    setColor(0)
    rectfill(0,-1, screenWidth, lerp(32.0,-1.0, gameTime.float / 100.0))
    rectfill(0,screenHeight+1, screenWidth, lerp(screenHeight.float - 32.0, screenHeight.float + 1.0, gameTime.float / 100.0))

  if gameTime > 300 and titlePosition > -34.0:
    titlePosition = lerp(titlePosition, -34.0, 0.05)
  elif introTextIndex == introText.high:
    titlePosition = clamp(lerp(titlePosition, 32.0, 0.05), -32, 32)

  if titlePosition > -32:
    shadowMode()
    sspr(0,96,128,32, -1, titlePosition)
    sspr(0,96,128,32, 1,  titlePosition)
    sspr(0,96,128,32, 0,  titlePosition - 1)
    sspr(0,96,128,32, 0,  titlePosition + 1)
    pal()
    sspr(0,96,128,32, 0,  titlePosition)

  # NOTE TEXT
  if currentNoteText != "":
    setColor(2)
    rectfill(0,screenHeight - 32, screenWidth, screenHeight)
    setColor(10)
    rect(1,screenHeight - 31, screenWidth - 2, screenHeight - 2)
    setColor(15)

    let text = currentNoteText.splitLines()
    var count = 0
    for i, line in text:
      if noteTextChar - count > 0:
        print(line[0..clamp(noteTextChar-count, 0, line.high)], 4, screenHeight - 29 + i * 8)
        count += line.len

  # INTRO TEXT
  if introTextIndex < introText.high:
    setColor(2)
    rectfill(0,screenHeight - 32, screenWidth, screenHeight)
    setColor(10)
    rect(1,screenHeight - 31, screenWidth - 2, screenHeight - 2)
    setColor(15)

    let text = introText[introTextIndex].splitLines()
    var count = 0
    for i, line in text:
      if introTextChar - count > 0:
        print(line[0..clamp(introTextChar-count,0,line.high)], 4, screenHeight - 29 + i * 8)
      count += line.len
    if introTextChar == introText[introTextIndex].high:
      setColor(if frame mod 60 < 30: 15 else: 10)
      print("[Z]", 4, screenHeight - 29 + 8 * text.len)

    #print(introText[introTextIndex][0..introTextChar], 4, screenHeight - 29)


proc introUpdate(dt: float32) =
  if btnp(pcStart) or btnp(pcA):
    nico.run(nil, gameUpdate, gameDraw)

var drippiness = 500

proc introDraw() =
  frame += 1
  if frame == 60:
    cls()
    synth(0, synSqr, 400, 4, -4)
    pitchbend(0, -2)
    sspr(104, 72, 24, 24, screenWidth div 2 - 12, screenHeight div 2 - 12)
  elif frame == 120:
    synth(0, synSqr, 400, 4, -4)
    pitchbend(0, -2)

    setColor(15)
    printc("ld40", 64, 92)
    printc("made in 48 hours", 64, 106)

  elif drippiness > 0:
    # do drippy effect
    for i in 0..<drippiness:
      let x = rnd(128)
      let y = rnd(128)
      let c = pget(x,y)
      if c == 8:
        if pget(x,y+1) != 15:
          pset(x,y+1,c)
          drippiness -= 1

  if frame >= 300:
    nico.run(nil, gameUpdate, gameDraw)

nico.init("impbox", "ld40")
nico.createWindow("cute cats daily", 128, 128, 4)
nico.run(gameInit, introUpdate, introDraw)


