import nico
import vec
import algorithm
import sequtils
import math
import tables
import astar
import hashes

{.this:self.}

# CONSTANTS

const friction = 0.25
const playerAccel = 10.0
const playerMaxSpeed = 2.0

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

type LitterBag = ref object of Movable
  serves: int

type FoodBag = ref object of Movable
  serves: int

type Cat = ref object of Movable
  color: range[0..2]
  targetPos: Vec2i
  boredom: float

  meow: bool

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

type Player = ref object of Movable
  holding: Entity

type Particle = object
  spr: int
  pos: Vec2f
  vel: Vec2f
  ttl: int
  text: string

# GLOBALS

var frame = 0
var objects: seq[Entity]
var player: Player
var particles: seq[Particle]
var tilemap: Tilemap
var money: int
var spinMoneyTimer: int
var nCats: int = 0

var nausea: float
var houseSmell: float

# INITIALISERS

proc newCat(pos: Vec2i): Cat =
  result = new(Cat)
  result.pos = pos
  result.color = rnd(3)
  result.targetPos = pos
  result.boredom = rnd(2.0)
  result.hitbox = (2,3,4,3)
  result.offset = vec2i(4, 6)
  result.state = Chill

  result.socialised = 0

  result.needToPoop = rnd(0.75)
  result.needToWee = rnd(0.75)

  nCats += 1

proc newBin(pos: Vec2i): Bin =
  result = new(Bin)
  result.pos = pos
  result.hitbox = (1,2,6,5)
  result.offset = vec2i(4, 6)

proc newBowl(pos: Vec2i): Bowl =
  result = new(Bowl)
  result.pos = pos
  result.hitbox = (2,4,4,2)
  result.offset = vec2i(4, 5)

proc newFoodBag(pos: Vec2i): FoodBag =
  result = new(FoodBag)
  result.pos = pos
  result.serves = 20
  result.hitbox = (2,4,3,4)
  result.offset = vec2i(3, 6)

proc newLitterBag(pos: Vec2i): LitterBag =
  result = new(LitterBag)
  result.pos = pos
  result.serves = 8
  result.hitbox = (1,2,6,5)
  result.offset = vec2i(4, 6)

proc newLitterBox(pos: Vec2i): LitterBox =
  result = new(LitterBox)
  result.pos = pos
  result.poop = 0
  result.wee = 0
  result.hasLitter = true
  result.hitbox = (1,1,6,5)
  result.offset = vec2i(4, 6)

proc newPlayer(pos: Vec2i): Player =
  result = new(Player)
  result.pos = pos
  result.hitbox = (2,5,4,7)
  result.offset = vec2i(4, 10)

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

# METHODS

proc isSolid(t: uint8): bool =
  case t:
  of 50,53,55,52,68,83:
    return false
  else:
    return true

proc isPathable(t: uint8): bool =
  case t:
  of 50,55,48,52,68,83:
    return true
  else:
    return false

proc isSolid(tx,ty: int): bool =
  if tx < 0 or ty < 0 or tx > 15 or ty > 15:
    return false
  return isSolid(mget(tx,ty))

proc isPathable(tx,ty: int): bool =
  if tx < 0 or ty < 0 or tx > 15 or ty > 15:
    return true
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

proc hotspot(self: Entity): Vec2i =
  return self.pos + self.offset

proc dist(a,b: Vec2f): float =
  return (a - b).length

proc dist(a,b: Entity): float =
  return (a.hotspot.vec2f - b.hotspot.vec2f).length

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

proc getName(self: Entity): string =
  if self of Cat:
    return "cat"
  if self of LitterBox:
    return "litter box"
  if self of LitterBag:
    return "litter bag"
  if self of Poop:
    return "poop"
  if self of Bin:
    return "bin"
  if self of FoodBag:
    return "food bag"
  if self of Bowl:
    return "cat bowl"
  return "?"

method getDescription(self: Entity): string {.base.} =
  return ""

method update(self: Entity, dt: float) {.base.} =
  discard

method drop(self: Entity): bool {.base.} =
  return true

method use(self: Entity) {.base.} =
  discard

method draw(self: Entity) {.base.} =
  setColor(8)
  circfill(pos.x, pos.y, 3)

method draw(self: Poop) =
  spr(5, pos.x, pos.y)

method draw(self: Bin) =
  spr(17, pos.x, pos.y)

method draw(self: Bowl) =
  spr(if foodServes > 0: 33 elif waterServes > 0: 34 else: 35, pos.x, pos.y)

method draw(self: LitterBox) =
  if not hasLitter:
    spr(24, pos.x, pos.y)
  else:
    spr(19 + min(poop,3), pos.x, pos.y)

method draw(self: LitterBag) =
  spr(38, pos.x, pos.y)

method draw(self: FoodBag) =
  spr(36, pos.x, pos.y)

method getDescription(self: LitterBag): string =
  return "serves: " & $self.serves

method getDescription(self: FoodBag): string =
  return "serves: " & $self.serves

method getDescription(self: Bowl): string =
  return "serves: " & $self.foodServes

method use(self: Bowl) =
  # check if it's near a bin, if so, empty it
  if self.foodServes > 0 or self.waterServes > 0:
    for obj in objects:
      if obj of Bin:
        if dist(obj,self) < 8:
          self.foodServes = 0
          self.waterServes = 0

method use(self: LitterBox) =
  # check if it's near a bin, if so, empty it
  if self.hasLitter:
    for obj in objects:
      if obj of Bin:
        if dist(obj,self) < 8:
          self.poop = 0
          self.wee = 0
          self.hasLitter = false

method use(self: Poop) =
  for obj in objects:
    if obj of Bin:
      if dist(obj,self) < 8:
        self.toKill = true
        return
    if obj of LitterBox and LitterBox(obj).hasLitter:
      if dist(obj,self) < 8:
        let box = LitterBox(obj)
        box.poop += 1
        self.toKill = true
        return

method use(self: FoodBag) =
  if serves > 0:
    for obj in objects:
      if obj of Bowl and Bowl(obj).foodServes < 4:
        if dist(obj,self) < 8:
          Bowl(obj).foodServes += 4
          serves -= 1
          return
  else:
    for obj in objects:
      if obj of Bin:
        if dist(obj,self) < 8:
          self.toKill = true
          return

method use(self: LitterBag) =
  # check if it's near a bin, if so, empty it
  if serves > 0:
    for obj in objects:
      if obj of LitterBox and not LitterBox(obj).hasLitter:
        if dist(obj,self) < 8:
          LitterBox(obj).hasLitter = true
          serves -= 1
          return
  else:
    for obj in objects:
      if obj of Bin:
        if dist(obj,self) < 8:
          self.toKill = true
          return

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

method draw(self: Player) =
  spr(16, pos.x, pos.y, 1, 2)

proc moveX(self: Movable, amount: float, start: float) =
  var step = amount.int.sgn
  for i in start..<abs(amount.int):
    if not self.isSolid(step, 0):
      pos.x += step
    else:
      # hit something
      vel.x = 0
      rem.x = 0

proc moveY(self: Movable, amount: float, start: float) =
  var step = amount.int.sgn
  for i in start..<abs(amount.int):
    if not self.isSolid(0, step):
      pos.y += step
    else:
      # hit something
      vel.y = 0
      rem.y = 0

method update(self: Movable, dt: float) =
  if Entity(self) == player.holding:
    vel = vec2f(0,0)
    pos = player.pos + player.offset - self.offset + vec2i(0, 1)
    return

  # check if on a solid tile, if so move them off it
  if self.isSolid(0,0):
    debug "standing in solid"
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

method update(self: Poop, dt: float) =
  procCall update(Movable(self), dt)

  if rnd(120) == 0:
    particles.add(Particle(spr: 7, pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, 0), vel: vec2f(0, -0.1), ttl: 30))

method update(self: LitterBox, dt: float) =
  if poop > 0:
    if rnd(600 / poop) == 0:
      particles.add(Particle(spr: 7, pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, 0), vel: vec2f(0, -0.1), ttl: 30))

  if wee > 0:
    if rnd(600 / wee) == 0:
      particles.add(Particle(spr: 8, pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, 0), vel: vec2f(0, -0.1), ttl: 30))

  procCall update(Movable(self), dt)

proc snap(pos: Vec2i): Vec2i =
  return vec2i((pos.x div 8) * 8, (pos.y div 8) * 8)

proc pathTo(self: Cat, goal: Vec2i) =
  targetPos = goal
  # try and find path to targetPos
  let start = getTile(self.hotspot())
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
    route = nil
    particles.add(Particle(text: "chill", pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, 0), vel: vec2f(0, -0.1), ttl: 60))
  of Sleep:
    route = nil
    particles.add(Particle(text: "sleep", pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, 0), vel: vec2f(0, -0.1), ttl: 60))
  of GoToToilet:
    toiletTimeout = 120
    route = nil
    particles.add(Particle(text: "toilet", pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, 0), vel: vec2f(0, -0.1), ttl: 60))
  of GoToEat:
    eatTimeout = 300
    route = nil
    particles.add(Particle(text: "eat", pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, 0), vel: vec2f(0, -0.1), ttl: 60))
  of Wander:
    route = nil
    particles.add(Particle(text: "wander", pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, 0), vel: vec2f(0, -0.1), ttl: 60))
  of Hyper:
    route = nil
    particles.add(Particle(text: "hyper", pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, 0), vel: vec2f(0, -0.1), ttl: 60))
  else:
    discard
  state = newState

method drop(self: Cat): bool =
  enterState(Wander)
  return true

method update(self: Cat, dt: float) =
  needToPoop += dt * 0.01 * rnd(1.0)
  needToWee += dt * 0.025 * rnd(1.0)
  needToEat += dt * 0.03 * rnd(1.0)
  needToSleep += dt * 0.005 * rnd(1.0)

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
    if route == nil:
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
    if route == nil:
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
    needToSleep -= dt * 0.005
    if needToSleep <= 0.0:
      enterState(Chill)
    if needToSleep < 0.25:
      if rnd(5000) == 0:
        enterState(Wander)

  of GoToEat:
    if usingObject != nil and usingObject of Bowl:
      let bowl = Bowl(usingObject)
      bowl.occupied = self
      if bowl.foodServes > 0:
        if frame mod 10 == 0:
          particles.add(Particle(text: "nom", pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, 0), vel: vec2f(0, -0.1), ttl: 20))
        eatTimeout -= 1
        if eatTimeout <= 0:
          bowl.foodServes -= 1
          bowl.occupied = nil
          usingObject = nil
          needToEat = 0
          enterState(Wander)

    if route == nil:
      # find a free bowl
      for obj in objects:
        if obj of Bowl:
          let bowl = Bowl(obj)
          if bowl.occupied == nil and bowl.foodServes > 0:
            pathTo(bowl.hotspot)
            break
      if route == nil:
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
              break

  of GoToToilet:
    if needToWee < 0.5 and needToPoop < 0.5:
      boredom = 0
      enterState(Hyper) # TODO should be charge around

    if usingObject != nil:
      if usingObject of LitterBox:
        let box = LitterBox(usingObject)
        box.occupied = self
        toiletTimeout -= 1

        if frame mod 10 == 0:
          particles.add(Particle(text: "poop", pos: self.hotspot.vec2f + vec2f(rnd(2.0)-1.0, 0), vel: vec2f(0, -0.1), ttl: 20))

        if toiletTimeout <= 0:
          box.occupied = nil
          usingObject = nil
          if needToPoop > 0.5:
            needToPoop = 0
            box.poop += 1
          if needToWee > 0.5:
            needToWee = 0
            box.wee += 1
          enterState(Wander)

    elif route == nil:
      var boxes = newSeq[LitterBox]()
      for obj in objects:
        if obj of LitterBox:
          let box = LitterBox(obj)
          if box.hasLitter:
            if box.poop < 5 and box.wee < 5:
              boxes.add(LitterBox(obj))

      debug "looking for poop box"
      boxes = boxes.sortedByIt(it.poop)
      debug "boxes: ", boxes.len
      while boxes.len > 0:
        pathTo(boxes[0].hotspot + vec2i(0, 3))
        debug "route: ", route
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

  if route != nil:
    if route.len == 0 or routeIndex > route.high:
      route = nil

    else:
      # try and find a new path if we get stuck
      routeTimeout -= 1
      if routeTimeout <= 0:
        pathTo(targetPos)

  # have to go right now
  if needToPoop > 1.0:
    objects.add(newPoop(pos))
    needToPoop = 0

  if needToWee > 1.0:
    objects.add(newWee(pos))
    needToWee = 0

  # follow route
  if route != nil and route.len > 0:
    let diff = (vec2f(route[routeIndex].x * 8 + 4, route[routeIndex].y * 8 + 4) - self.hotspot.vec2f)
    let d = diff.length

    if mget(route[routeIndex].x, route[routeIndex].y) == 48:
      meow = true
    else:
      if meow:
        particles.add(Particle(spr: 43, pos: self.hotspot.vec2f, vel: vec2f(0, -0.1), ttl: 30))
      meow = false

    if d < 0.5:
      routeIndex += 1
      if routeIndex > route.high:
        route = nil
        routeIndex = 0

    else:
      vel += diff.normalized() * (if state == Wander: 5.0 elif state == Hyper: 15.0 else: 10.0)

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
    spr(3, pos.x, pos.y)
  of Chill:
    spr(2, pos.x, pos.y)
  else:
    spr(if vel.length > 0.5: 1 else: 0, pos.x, pos.y)
  pal()

  if meow:
    setColor(6)
    printc("!", pos.x + 4, pos.y - 5)

  when true:
    if route != nil:
      setColor(6)
      for i in (routeIndex+1)..<route.len:
        line(route[i-1].x * 8 + 4, route[i-1].y * 8 + 4, route[i].x * 8 + 4, route[i].y * 8 + 4)

      setColor(14)
      circ(targetPos.x, targetPos.y, 4)

# GAME

proc gameInit() =
  loadPaletteFromGPL("palette.gpl")
  loadSpritesheet("spritesheet.png")

  loadMap("map.json")

  money = 500

  objects = newSeq[Entity]()

  for y in 0..15:
    for x in 0..15:
      let t = mget(x,y)
      if t == 17:
        objects.add(newBin(vec2i(x*8, y*8)))
        mset(x,y,50)
      elif t == 19:
        objects.add(newLitterBox(vec2i(x*8, y*8)))
        mset(x,y,50)
      elif t == 38:
        objects.add(newLitterBag(vec2i(x*8, y*8)))
        mset(x,y,50)
      elif t == 16:
        debug "found player"
        player = newPlayer(vec2i(x*8, y*8))
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

proc gameUpdate(dt: float) =
  frame += 1

  if frame mod (30 * 60) == 0:
    money += nCats * 5
    spinMoneyTimer += 30

  if spinMoneyTimer > 0:
    spinMoneyTimer -= 1

  # input for player
  if btn(pcLeft):
    player.vel.x -= playerAccel
  if btn(pcRight):
    player.vel.x += playerAccel
  if btn(pcUp):
    player.vel.y -= playerAccel
  if btn(pcDown):
    player.vel.y += playerAccel

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
        if tile.t == 55:
          synth(0, synNoise, 1000, 2, -2)
          pitchbend(0, 1)

          # TODO: check if door is blocked
          mset(tile.x, tile.y, 48)
          break
    else:
      player.holding.use()

  if btnp(pcA):
    if player.holding == nil:
      # search for the nearest object and hold it
      var nearestDist = Inf
      var nearestObj: Entity
      for obj in objects:
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
      if nearestObj != nil:
        player.holding = nearestObj
        synth(0, synSqr, 100.0, 4, -2)
        pitchbend(0, 10)
    else:
      if player.holding.drop():
        player.holding.pos = snap(player.hotspot)
        player.holding = nil
        synth(0, synSqr, 100.0, 4, -2)
        pitchbend(0, -10)
      else:
        synth(0, synNoise, 1000.0, 2, -3)
        pitchbend(0, -1)


  for i in 0..<objects.len:
    objects[i].update(dt)

  for p in mitems(particles):
    p.ttl -= 1
    p.pos += p.vel

  particles = particles.filterIt(it.ttl > 0)

  objects = objects.filterIt(not it.toKill)

  nausea *= 0.9

  houseSmell = 0

  for obj in objects:
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

proc gameDraw() =
  setColor(3)
  rectfill(0,0,screenWidth, screenHeight)

  mapDraw(0,0,16,16,0,0)

  objects = objects.sortedByIt(it.pos.y + it.hitbox.y + it.hitbox.h)

  for obj in objects:
    obj.draw()
    setColor(6)
    #rect(obj.pos.x + obj.hitbox.x, obj.pos.y + obj.hitbox.y, obj.pos.x + obj.hitbox.x + obj.hitbox.w - 1, obj.pos.y + obj.hitbox.y + obj.hitbox.h - 1)

  for p in particles:
    if p.text != nil:
      printc(p.text, p.pos.x, p.pos.y)
    else:
      spr(p.spr, p.pos.x - 4, p.pos.y - 7)

  setColor(14 + (if spinMoneyTimer > 0 and  frame mod 10 < 5: 1 else: 0))
  printr($money, screenWidth - 8, 1)
  spr(73 + (if spinMoneyTimer > 0: (frame div 10) mod 4 else: 0), screenWidth - 8, 0)

  setColor(0)
  rectfill(1,1,1+houseSmell.int,6)

  if player.holding != nil:
    setColor(15)
    printr(player.holding.getName, screenWidth - 4, screenHeight - 14)
    printr(player.holding.getDescription, screenWidth - 4, screenHeight - 8)

  for i in 0..<min(nausea.int,20):
    glitchBlur(0,0,screenWidth,screenHeight,1)

nico.init("impbox", "ld40")
nico.createWindow("ld40", 128, 128, 4)
nico.run(gameInit, gameUpdate, gameDraw)
