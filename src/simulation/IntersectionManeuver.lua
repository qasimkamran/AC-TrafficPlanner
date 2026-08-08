local TrafficConfig = require('TrafficConfig')
local MathUtils  = require('MathUtils')
local CachingCurve = require('CachingCurve')
local ManeuverBase = require('ManeuverBase')
local IntersectionLink = require('IntersectionLink')
local DistanceTags = require('DistanceTags')

---@param item IntersectionManeuver
local function _highlightFlash(item, r, g, b)
  if TrafficConfig.debugBehaviour then
    local driver = item.guide:getDriver()
    if driver:getCar() == nil then return end
    driver:getCar():setDebugValue(r, g, b)
    setTimeout(function () 
      if driver:getCar() == nil then return end
      driver:getCar():setDebugValue()
    end, 0.3)
  end
end

---@class IntersectionManeuver : ManeuverBase
---@field inter TrafficIntersection
---@field phase integer
---@field guide TrafficGuide
---@field fromDef IntersectionLink
---@field toDef IntersectionLink
---@field _minContact any
---@field _trajectoryPriority number
---@field makingUTurn boolean
local IntersectionManeuver = class('IntersectionManeuver', ManeuverBase, class.Pool)

local lastIndex = 0
local _mrandom = math.random
local feederHoldback = 0
local feederSecondCarSafetyTime = 2

local function estimateAccelerationTravelTime(distance, speedKmh, targetSpeedKmh, initialDelay)
  local time = initialDelay or 0
  local step = 0.1
  while distance > 0 and time < 30 do
    speedKmh = speedKmh + (targetSpeedKmh - speedKmh) * 0.06
    distance = distance - math.max(speedKmh, 0) / 3.6 * step
    time = time + step
  end
  return time
end

local function feederLogValue(value)
  return tostring(value == nil and '?' or value):gsub('[\r\n\t]', ' ')
end

local function appendFeederStallLog(item, reason)
  if not TrafficPlannerFeederLogFilename then return end
  local parts = {}
  local function add(key, value)
    parts[#parts + 1] = key..'='..feederLogValue(value)
  end

  local driver = item.guide:getDriver()
  local exitClearance = item.toDef.lane:distanceToNextCar(item.toDef.to, driver.dimensions.front)
  add('time', os.date('%Y-%m-%d %H:%M:%S'))
  add('reason', reason)
  add('stoppedFor', string.format('%.1f', item._feederStoppedFor))
  add('speedKmh', string.format('%.2f', driver:getSpeedKmh()))
  add('intersection', item.inter.name)
  add('feeder', item.fromDef.lane.name)
  add('output', item.toDef.lane.name)
  add('distanceToEntry', string.format('%.2f', math.max(-item._inCurve, 0)))
  add('curveLength', string.format('%.2f', item.curveInfo.curve.length))
  add('clearanceTime', item._feederClearanceTime and string.format('%.2f', item._feederClearanceTime) or '?')
  add('trafficLookahead', item._feederTrafficSafetyTime
    and string.format('%.2f', item._feederTrafficSafetyTime) or '?')
  add('exitClearance', string.format('%.2f', exitClearance))
  add('mandatoryWait', string.format('%.2f', item._feederWaitTime))
  add('exitBlocked', item._roundaboutExitBlocked)
  add('engaged', item.inter.engaged.length)
  add('traversing', item.inter.traversing.length)

  for i = 1, item.inter.engaged.length do
    local other = item.inter.engaged[i]
    if other ~= item then
      local otherDriver = other.guide:getDriver()
      add('other'..i, string.format('%s,active=%s,feeder=%s,roundabout=%s,inCurve=%.2f,speed=%.2f,output=%s',
        feederLogValue(other.fromDef.lane.name), tostring(other.active), tostring(other.fromDef.lane.feederLane),
        tostring(other:isRoundaboutFlow()), other._inCurve, otherDriver:getSpeedKmh(), feederLogValue(other.toDef.lane.name)))
    end
  end

  pcall(function ()
    local filename = TrafficPlannerFeederLogFilename
    local previous = io.load(filename, '')
    if #previous > 750000 then previous = previous:sub(-500000) end
    io.save(filename, previous..table.concat(parts, '\t')..'\n')
  end)
end

---@param intersection TrafficIntersection
---@param guide TrafficGuide
---@param fromDef IntersectionLink
---@param toDef IntersectionLink
---@return IntersectionManeuver
function IntersectionManeuver:initialize(intersection, guide, fromDef, toDef)
  if self.inter then error('Already attached') end

  lastIndex = lastIndex + 1

  local curveInfo = intersection:getCachingCurve(fromDef, toDef)
  self.inter = intersection
  self.phase = intersection.phase
  self.guide = guide
  self.fromDef = fromDef
  self.toDef = toDef
  self._roundaboutFlow = intersection.roundabout or fromDef.lane.roundabout or toDef.lane.roundabout
  self._inCurve = -fromDef.lane:distanceToUpcoming(guide:getDistance(), fromDef.from)
  self.active = false
  self.closeToTraverse = false
  self._trajectoryPriority = intersection.mergingIntersection and _mrandom() or intersection:getPriorityLevel(fromDef.lane, toDef.lane)
  self._trajectoryOffsetPriority = lastIndex
  self._checkDelay = 0
  self._blockedCounter = 0
  self._impatienceCounter = 0
  self._engagedFor = 0
  self.justFloorIt = false
  self._feederWaitTime = 0
  self._feederWaitComplete = not fromDef.lane.feederLane
  self._roundaboutExitBlocked = false
  self._feederStoppedFor = 0
  self._feederLastLogAt = 0
  self._feederLastLogReason = nil
  self._feederStopReason = 'approaching'
  self._feederClearanceTime = nil
  self._feederTrafficSafetyTime = nil
  self.makingUTurn = curveInfo.curve.fromDir:dot(curveInfo.curve.toDir) < -0.5
  self.curveInfo = curveInfo
  self._minContact = { distance = 1e9 }
end

function IntersectionManeuver:__tostring()
  return string.format('<IntersectionManeuver: %s, priority=%.2f, phase=%s>', 
    not self.closeToTraverse and 'far' or not self.active and 'waiting' or 'traversing',
    self._trajectoryPriority, self.phase)
end

function IntersectionManeuver:isRoundaboutFlow()
  return self._roundaboutFlow == true
end

function IntersectionManeuver:isRoundaboutFeederBlocked()
  if not self:isRoundaboutFlow() or not self.fromDef.lane.feederLane then return false end

  local ownDriver = self.guide:getDriver()
  local meta = self.guide:getMeta()
  local feederDistanceToOutput = math.max(-self._inCurve, 0) + self.curveInfo.curve.length
  local feederTargetSpeed = meta and meta.speedLimit
    and math.min(ownDriver.maxSpeed, meta.speedLimit + 5) or ownDriver:getSpeedKmh()
  local mandatoryWaitLeft = math.max(0, 0.5 - self._feederWaitTime)
  local feederClearanceTime = estimateAccelerationTravelTime(feederDistanceToOutput,
    ownDriver:getSpeedKmh(), feederTargetSpeed, mandatoryWaitLeft) + 0.5
  self._feederClearanceTime = feederClearanceTime
  -- Do not enter on the tail of the first available gap. Reserve enough
  -- look-ahead to account for a second circulating car following close behind.
  local circulatingSafetyTime = feederClearanceTime + feederSecondCarSafetyTime
  self._feederTrafficSafetyTime = circulatingSafetyTime
  local engaged = self.inter.engaged
  for i = 1, engaged.length do
    local other = engaged[i]
    if other ~= self and other:isRoundaboutFlow() then
      local pathsConflict = other.toDef == self.toDef or self.curveInfo:intersects(other.curveInfo)
      local otherDriver = other.guide:getDriver()
      local otherMeta = other.guide:getMeta()
      local otherSpeed = math.max(otherDriver:getSpeedKmh(),
        otherMeta and otherMeta.speedLimit + 5 or 0) / 3.6
      local otherArrivalTime = otherSpeed > 0.1 and math.max(-other._inCurve, 0) / otherSpeed or 1e9
      -- A feeder which is already traversing still needs physical clearance, but
      -- queued feeders must not grant priority to each other as if they were
      -- established roundabout traffic. Exit reservations order those cars.
      local otherIsFeeder = other.fromDef.lane.feederLane
      -- Curve geometry is authoritative here. On a curved roundabout approach
      -- a conflicting car can rotate past the entry's instantaneous "right"
      -- half-plane before reaching the crossing point, which previously let
      -- feeders at intersections such as #11 enter prematurely.
      if pathsConflict and (other.active or not otherIsFeeder
          and otherArrivalTime <= circulatingSafetyTime) then
        return true
      end
    end
  end

  local links = self.inter._linksList
  for i = 1, links.length do
    local link = links[i]
    -- Some approaches are deliberately marked as both feeder and roundabout.
    -- Only established, non-feeder lanes have UK roundabout right of way.
    if link.fromPos ~= nil and link.lane.roundabout
        and not link.lane.feederLane and link.lane ~= self.fromDef.lane then
      local cars = link.lane.orderedCars
      for j = 1, cars.length do
        local cursor = cars[j]
        if cursor.driver ~= ownDriver then
          local distance = link.lane:distanceToUpcoming(cursor.distance, link.from)
          local speed = math.max(cursor.driver:getSpeedKmh(), cursor.edgeMeta.speedLimit + 5) / 3.6
          -- Any established roundabout approach attached to this intersection
          -- has priority during the safety window. Engaged maneuvers above add
          -- exact path filtering; this scan catches the next one or two cars
          -- before their maneuver has been created.
          if distance >= 0 and speed > 0.1
              and distance / speed <= circulatingSafetyTime then return true end
        end
      end
    end
  end
  return false
end

function IntersectionManeuver:selectSafeRoundaboutExit()
  if not self:isRoundaboutFlow() or not self.guide:canChange() then return end

  local bestLink, bestCurve, bestClearance = nil, nil, -1
  local ownDriver = self.guide:getDriver()
  local meta = self.guide:getMeta()
  local selectionSpeed = math.max(ownDriver:getSpeedKmh(), meta and meta.speedLimit + 5 or 0)
  local minimumExitClearance = math.max(10, selectionSpeed / 3.6 * 1.5)
  local hasPriorityOverFeeders = not self.fromDef.lane.feederLane
  local links = self.inter._linksList
  for i = 1, links.length do
    local candidate = links[i]
    if candidate.toPos ~= nil
        and self.inter:areLanesCompatible(self.fromDef.lane, candidate.lane, true) then
      local candidateCurve = self.inter:getCachingCurve(self.fromDef, candidate)
      local crossing, reserved = false, false
      for j = 1, self.inter.engaged.length do
        local other = self.inter.engaged[j]
        local otherIsFeeder = other.fromDef.lane.feederLane
        local feederAhead = other._inCurve > self._inCurve + 0.1
          or math.abs(other._inCurve - self._inCurve) <= 0.1
            and other._trajectoryOffsetPriority < self._trajectoryOffsetPriority
        local ignoreOther = otherIsFeeder and hasPriorityOverFeeders
          or not other.active and not feederAhead
        if other ~= self and not ignoreOther then
          if other.toDef == candidate then reserved = true end
          if other.fromDef ~= self.fromDef and candidateCurve:intersects(other.curveInfo) then
            crossing = true
          end
        end
      end

      if not crossing and not reserved then
        local clearance = candidate.lane:distanceToNextCar(candidate.to,
          ownDriver.dimensions.front)
        if clearance >= minimumExitClearance and clearance > bestClearance then
          bestLink, bestCurve, bestClearance = candidate, candidateCurve, clearance
        end
      end
    end
  end

  self._roundaboutExitBlocked = bestLink == nil
  if bestLink ~= nil then
    if bestLink ~= self.toDef then
      self.toDef = bestLink
      self.curveInfo = bestCurve
      self.makingUTurn = bestCurve.curve.fromDir:dot(bestCurve.curve.toDir) < -0.5
      self._roundaboutFlow = self.inter.roundabout or self.fromDef.lane.roundabout or bestLink.lane.roundabout
      self.guide:changeNextTo(bestLink.lane, bestLink.to)
    end
  end
end

function IntersectionManeuver:detach()
  self.inter:disconnectEngaged(self)
  self.inter = nil
  class.recycle(self)
end

local _mmin = math.min

---@param laneLink IntersectionLink
---@param iman IntersectionManeuver
local function findFreeAlternativeCallback(laneLink, _, iman)
  if laneLink.lane ~= iman.toDef.lane
    and laneLink.toPos ~= nil then
    local distance = laneLink.lane:distanceToNextCar(laneLink.to)
    if iman.inter:areLanesCompatible(iman.fromDef.lane, laneLink.lane, true) then
      return _mmin(distance, 100)
    end
  end
  return 0
end

---@return IntersectionLink
function IntersectionManeuver:_findFreeAlternative()
  if not self.guide:canChange() then return nil end
  -- if self.inter.name == 'I29' then ac.debug('looking for a way around', math.random()) end
  return self.inter._linksList:random(findFreeAlternativeCallback, self)
end

---@param e IntersectionManeuver
---@param n CachingCurve
local function findWayAroundNarrowCallback(e, _, n)
  return not n:intersects(e.curveInfo)
end

function IntersectionManeuver:_findWayAroundNarrow()
  local newLaneLink = self:_findFreeAlternative()
  self._impatienceCounter = 0
  if newLaneLink ~= nil then
    local newCurveInfo = self.inter:getCachingCurve(self.fromDef, newLaneLink)
    if self.inter.traversing:every(findWayAroundNarrowCallback, newCurveInfo) then
      self.toDef = newLaneLink
      self.curveInfo = newCurveInfo
      self:activate()
      self.guide:changeNextTo(self.toDef.lane, self.toDef.to)
      return true
    end
  end
  return false
end

function IntersectionManeuver:_findWayAroundWide()
  self._impatienceCounter = 0
  local newLaneLink = self:_findFreeAlternative()
  if newLaneLink ~= nil then
    local dir = self.guide:getDriver():getDirRef()
    if dir == nil then return end
    local newCurveInfo = CachingCurve(
      self.guide:getDriver():getPosRef(), dir,
      newLaneLink.lane:interpolateDistance(newLaneLink.to), newLaneLink.lane:getDirection(newLaneLink.to), true)
    if self.inter.traversing:every(function (e) return e == self or not newCurveInfo:intersects(e.curveInfo) end) then
      self.toDef = newLaneLink
      self.curveInfo = newCurveInfo
      self:activate()
      self.guide:changeNextTo(self.toDef.lane, self.toDef.to)
      -- if self.inter.name == 'I29' then
        -- ac.debug('found a wide way around', math.random()) 
        -- DebugShapes['_findWayAroundWide: FROM'] = self.guide:getDriver():getPosRef():clone()
        -- DebugShapes['_findWayAroundWide: FROM'] = newLaneLink.toPos:clone()
      -- end
      return
    end
    class.recycle(newCurveInfo)
  end
end

local _mucrossY = MathUtils.crossY
local _dpos = vec3()

---@param a IntersectionManeuver
---@param b IntersectionManeuver
local function _compareTrajectories(a, b)
  if not a.makingUTurn and not b.makingUTurn then return 0 end
  local aUTurnLp = a.makingUTurn and a.toDef.toPos:distanceSquared(b.fromDef.fromPos) < a.fromDef.fromPos:distanceSquared(b.fromDef.fromPos) * 0.7
  local bUTurnLp = b.makingUTurn and b.toDef.toPos:distanceSquared(a.fromDef.fromPos) < b.fromDef.fromPos:distanceSquared(a.fromDef.fromPos) * 0.7
  return aUTurnLp == bUTurnLp and 0 or bUTurnLp and 1 or -1
end

---@param engagement IntersectionManeuver
function IntersectionManeuver:_hasPriorityOver(engagement)
  if self.fromDef.tlState > 0 then return true end

  if self._trajectoryPriority ~= engagement._trajectoryPriority then
    return (self._trajectoryPriority or 0) > (engagement._trajectoryPriority or 0)
  end

  -- If starting from the same point or our lane is currently blocked, can’t have a priority
  if self.fromDef.lane == engagement.fromDef.lane or self.fromDef.tlState < 0 then return false end

  -- If starting with similar direction, same priority
  if self.curveInfo.curve.fromDir:dot(engagement.curveInfo.curve.fromDir) > 0.8 then
    return false
  end

  -- Compare trajectories: somebody making a U-turn in a certain way would have to wait
  -- local comparisonResult = _compareTrajectories(self, engagement)
  -- if comparisonResult ~= 0 then
  --   return comparisonResult > 0
  -- end
  if engagement.makingUTurn ~= self.makingUTurn then
    return engagement.makingUTurn
  end

  -- If other car is on the right side of us, can’t have a priority
  return _mucrossY(self.curveInfo.curve.fromDir, _dpos:set(engagement.fromDef.fromPos):sub(self.fromDef.fromPos)) < 0
end

---@param engagement IntersectionManeuver
---@param greenLightMode boolean 
function IntersectionManeuver:_compatibleWith(engagement, greenLightMode)
  if self.fromDef == engagement.fromDef -- start from the same position
      -- or greenLightMode and self.inter.phase == engagement.phase -- green light: ignore trajectories and just go -- TODO:DEV
      or self.inter.mergingIntersection and engagement.active -- merging intersections work differently
      or not self.curveInfo:intersects(engagement.curveInfo) then -- if trajectories do not intersect, all is good
    return true
  end

  -- if trajectories intersect, last chance: maybe _remaining_ bits of trajectories don’t?
  -- if self._engagedFor > 5 and engagement._inCurve > 6 and not self.curveInfo:intersectsAfter(engagement.curveInfo, self._inCurve + 3, engagement._inCurve) then
  --   _highlightFlash(self, 1, 0, 1)
  --   -- local e = engagement
  --   -- for j = 0, 20 do
  --   --   DebugShapes['pe'..tostring(j)] = e.curveInfo.curve:get(math.lerp(e._inCurve, e.curveInfo.curve.length, j/20))
  --   --   DebugShapes['ps'..tostring(j)] = e.curveInfo.curve:get(math.lerp((self._inCurve + 3), self.curveInfo.curve.length, j/20))
  --   -- end
  --   return true
  -- end

  -- nope, have to wait
  return false
end

function IntersectionManeuver:_compatibleWithTraversing(greenLightMode)
  local ts = self.inter.traversing
  local tn = ts.length
  for i = 1, tn do
    local e = ts[i]
    if not self:_compatibleWith(e, greenLightMode) then
      return false
    end
  end
  return true
end

function IntersectionManeuver:_anyBlocking()
  local es = self.inter.engaged
  local en = es.length
  for i = 1, en do
    local other = es[i]
    if other.closeToTraverse and not other.active and other:_hasPriorityOver(self) and not self:_compatibleWith(other) then
      return other
    end
  end
  return nil
end

function IntersectionManeuver:_shouldLetOthersFirst()
  local bc = self._blockedCounter
  if bc > 4 then
    _highlightFlash(self, 0, 1, 1)
    return false
  end

  if self._impatienceCounter > 2 and self.inter.traversing:some(function (i) return i.fromDef == self.fromDef and i.toDef == self.toDef end) then
    _highlightFlash(self, 0, 1, 1)
    return false
  end

  local blocking = self:_anyBlocking()
  if blocking == nil then 
    _highlightFlash(self, 0, 1, 0)
    return false
  end

  _highlightFlash(self, 1, 0, 0)
  _highlightFlash(blocking, 1, 1, 0)

  self._blockedCounter = bc + 1
  self._impatienceCounter = 0
  return true
end

function IntersectionManeuver:_checkIfShouldGo(speedKmh, dt)
  local fromDef = self.fromDef
  local inter = self.inter

  -- if inter.phase ~= inter.lowestPhase then return false end -- TODO

  -- Red light or something like that
  local tlState = fromDef.tlState
  if tlState < 0 or tlState > 0 and inter.phase == inter.lowestPhase then
    return tlState > 0 and (tlState == IntersectionLink.StateGreen or self._inCurve > -4)
  end

  if not self:_compatibleWithTraversing(tlState == IntersectionLink.StateGreen) then

    -- Got tired of waiting and found a different route
    if self._impatienceCounter > 5 and speedKmh < 0.01 and self:_findWayAroundNarrow() then
      _highlightFlash(self, 0, 0, 0.5)
      return true
    end

    -- Somebody is currently traversing intersection in an incompatible manner
    if self._blockedCounter > 1 then
      self._blockedCounter = 4
    end

    _highlightFlash(self, 0.3, 0, 0)
    return false

  end

  -- Letting go a car on the right side
  if tlState == IntersectionLink.StateAuto and self:_shouldLetOthersFirst() then
    return false
  end

  return true
end

function IntersectionManeuver:activate()
  if not self.active then
    self.active = true
    self.phase = self.inter.phase
    self.inter.traversing:push(self)
  end
end

function IntersectionManeuver:advance(speedKmh, dt)
  local active = self.active
  local closeToTraverse = self.closeToTraverse
  local _inCurve = self._inCurve + (speedKmh / 3.6) * dt
  self._inCurve = _inCurve
  self._engagedFor = self._engagedFor + dt

  if self.fromDef.lane.feederLane and not self.active and speedKmh < 0.5 then
    self._feederStoppedFor = self._feederStoppedFor + dt
    local reason = self._feederStopReason or 'unknown'
    if self._feederStoppedFor >= 3 and (reason ~= self._feederLastLogReason
        or self._feederStoppedFor - self._feederLastLogAt >= 5) then
      appendFeederStallLog(self, reason)
      self._feederLastLogAt = self._feederStoppedFor
      self._feederLastLogReason = reason
    end
  elseif speedKmh >= 0.5 then
    self._feederStoppedFor = 0
    self._feederLastLogAt = 0
    self._feederLastLogReason = nil
  end

  if not active and self:isRoundaboutFlow() then self:selectSafeRoundaboutExit() end

  if not self._feederWaitComplete then
    local distanceToHold = -_inCurve - feederHoldback
    if speedKmh < 0.5 and distanceToHold < 6 then
      self._feederWaitTime = self._feederWaitTime + dt
      if self._feederWaitTime >= 0.5 then self._feederWaitComplete = true end
    elseif speedKmh >= 0.5 then
      self._feederWaitTime = 0
    end
  end

  if active or closeToTraverse then
    self._impatienceCounter = self._impatienceCounter + dt
  end

  if not closeToTraverse and _inCurve > -2 then
    closeToTraverse, self.closeToTraverse = true, true
  end

  if not active and speedKmh > 10
      and self._trajectoryPriority >= 0 
      and self.guide._curCursor and self.guide._curCursor.index == 1
      and self.fromDef.tlState == IntersectionLink.StateGreen 
      and self.inter.phase == self.inter.lowestPhase then
    active, self.justFloorIt = true, true
    self:activate()
  end

  if not active and closeToTraverse then
    if self:isRoundaboutFlow() and not self._roundaboutExitBlocked
        and self._feederWaitComplete and not self:isRoundaboutFeederBlocked() then
      active = true
      self:activate()
    elseif not self:isRoundaboutFlow() and self._feederWaitComplete then
      local checkDelay = self._checkDelay - dt
      if checkDelay > 0 then
        self._checkDelay = checkDelay
      elseif self:_checkIfShouldGo(speedKmh, dt) then
        active = true
        self:activate()
      else
        self._checkDelay = 0.5
      end
    end
  end

  if active then
    if _inCurve > self.curveInfo.curve.length then
      self:detach()
      return true
    end

    if speedKmh < 0.01 and self._impatienceCounter > 5 and not self:shouldDetachFromLane() and self.guide:getDriver():getDirRef() ~= nil then
      self:_findWayAroundWide()
      return false
    end
  end

  return false
end

function IntersectionManeuver:shouldDetachFromLane()
  return self._inCurve > 5
end

function IntersectionManeuver:ensureActive()
  if self._inCurve < 0 then
    self._inCurve = 0
  end
end

function IntersectionManeuver:calculateCurrentPosInto(v, estimate)
  if self._inCurve >= 0 then
    return self.curveInfo.curve:getInto(v, self._inCurve, estimate)
  else
    if self.guide._curCursor == nil then
      if DebugShapes then DebugShapes.unexpected = self.guide.driver:getPosRef():clone() end
      error('Guide lost its cursor, but intersection meaneuver is yet to start')
    else
      -- TODO: Seems like maneuver and lane go out of sync, so this line fixes occasional jumps, but why?
      self._inCurve = -self.fromDef.lane:distanceToUpcoming(self.guide:getDistance(), self.fromDef.from)
    end
  end
  return nil
end

function IntersectionManeuver:handlesDistanceToNext()
  return self.active
end

local _refFuturePos = vec3()
local _futureDirHint = vec3()
local _relativeTrafficPos = vec3()
local _needsMinContact = false

---@param driver TrafficDriver
---@param otherDriver TrafficDriver
local function _distanceBetween(driver, otherDriver, futurePosHint)
  local car = driver:getCar()
  local otherCar = otherDriver:getCar()
  if car == nil or otherCar == nil then return 0 end
  return car:freeDistanceTo(otherCar, _futureDirHint:set(futurePosHint):sub(car:getPosRef()):addScaled(car:getDirRef(), 6):normalize())
end

---@return number, CarBase|nil, DistanceTag
function IntersectionManeuver:distanceToNextCar()
  local roundaboutFlow = self:isRoundaboutFlow()
  -- Exit reservations are an admission gate for feeder traffic. Established
  -- roundabout traffic keeps its selected route and must not brake to yield to
  -- a feeder or another tentative reservation at the next intersection.
  local exitBlocked = not self.active and self.fromDef.lane.feederLane
    and self._roundaboutExitBlocked
  local feederMandatoryStop = not self.active and not self._feederWaitComplete
  local feederBlocked = not self.active and self:isRoundaboutFeederBlocked()
  local mustWait = exitBlocked or feederMandatoryStop or feederBlocked
  local freeRoundaboutFlow = roundaboutFlow and not mustWait
  local distanceToEntry = -self._inCurve - (mustWait and feederHoldback or 0)
  local rd, rc, rt = freeRoundaboutFlow and 1e9 or distanceToEntry, nil,
    exitBlocked and DistanceTags.IntersectionRoundaboutExitBlocked
      or feederMandatoryStop and DistanceTags.IntersectionFeederMandatoryStop
      or feederBlocked and DistanceTags.IntersectionRoundaboutFeederYield
      or freeRoundaboutFlow and DistanceTags.IntersectionActive or DistanceTags.IntersectionDistanceTo
  self._feederStopReason = exitBlocked and 'roundabout-exit-clearance'
    or feederMandatoryStop and 'mandatory-half-second-stop'
    or feederBlocked and 'right-side-roundabout-gap'
    or not self.active and 'intersection-priority-or-conflict' or 'active'
  local justFloorIt = self.justFloorIt
  if justFloorIt and not roundaboutFlow then
    local eng = self.inter.engaged
    for i = 1, #eng do
      local e = eng[i]
      if e.fromDef ~= self.fromDef and e._trajectoryPriority > self._trajectoryPriority then
        justFloorIt = false
        break
      end
    end
    if justFloorIt then
      rd, rt = 40, DistanceTags.IntersectionDrivingStraightWithPriority
    end
  end

  if self.closeToTraverse then
    if self.active then
      rd, rt = freeRoundaboutFlow and 1e9 or 40, DistanceTags.IntersectionActive
    end

    local _inCurve = self._inCurve

    local curveLeft = self.curveInfo.curve.length - _inCurve
    if curveLeft < 8 then
      local dd, dc, dt = self.toDef.lane:distanceToNextCar(self.toDef.to - curveLeft, self.guide:getDriver().dimensions.front)
      if dd < rd then
        rd, rc, rt = dd, dc, dt
        -- self.driver._nextTag = desiredTag

        if self._minContact.mainCar ~= nil then
          self._minContact.active = false
        end
      end
    end

    -- self.driver._nextTag = 'inter: min-none'

    if self._minContact.mainCar ~= nil then
      self._minContact.active = false
    end

    local _trajectoryPriority = _inCurve > 0 and self._trajectoryPriority or 0
    self.curveInfo.curve:getInto(_refFuturePos, _inCurve + 4, true)

    local ts = self.inter.traversing
    local tn = ts.length
    local fromSameSide = 0
    local ignoreFeederTraffic = roundaboutFlow and not self.fromDef.lane.feederLane
    for i = 1, tn do
      local e = ts[i]
      if e ~= self and not (ignoreFeederTraffic and e.fromDef.lane.feederLane) then

        if not roundaboutFlow and _trajectoryPriority < 0 then
          if e.fromDef.enterSide == self.fromDef.enterSide then
            fromSameSide = fromSameSide + 1
          elseif (e._trajectoryPriority > self._trajectoryPriority or e._trajectoryPriority == self._trajectoryPriority and self._trajectoryOffsetPriority < e._trajectoryOffsetPriority) 
              and self.curveInfo:intersects(e.curveInfo)
              and self.curveInfo:intersectsAfter(e.curveInfo, self._inCurve + 3, e._inCurve) 
              then
            -- ac.debug('here', self.curveInfo:intersectsAfter(e.curveInfo, self._inCurve + 3, e._inCurve))
            -- if not self.curveInfo:intersectsAfter(e.curveInfo, self._inCurve + 3, e._inCurve) then
            --   for j = 0, 20 do
            --     DebugShapes['pe'..tostring(j)] = e.curveInfo.curve:get(math.lerp(e._inCurve, e.curveInfo.curve.length, j/20))
            --     DebugShapes['ps'..tostring(j)] = e.curveInfo.curve:get(math.lerp((self._inCurve + 3), self.curveInfo.curve.length, j/20))
            --   end
            -- end

            local d = 4 - _inCurve
            if d < rd then
              rd, rc, rt = d, e.guide:getDriver():getCar(), DistanceTags.IntersectionWaitingOnSecondaryRoute
            end
          end
        end

        local eDriver = e.guide:getDriver()
        -- Once a feeder has been admitted it is committed to the roundabout.
        -- Nearby traffic behind it must not make it hesitate after setting off;
        -- cars genuinely ahead and output-lane occupancy are still respected.
        local committedFeeder = self.active and roundaboutFlow and self.fromDef.lane.feederLane
        local relativeTrafficPos = _relativeTrafficPos:set(eDriver:getPosRef())
          :sub(self.guide:getDriver():getPosRef())
        local trafficIsAhead = not committedFeeder
          or relativeTrafficPos:dot(self.guide:getDriver():getDirRef()) > 0
        if trafficIsAhead and eDriver.pos:closerToThan(_refFuturePos, 6) then
          local d = _distanceBetween(self.guide:getDriver(), eDriver, _refFuturePos)
          if d < rd then
            rd, rc, rt = d, eDriver:getCar(), e.fromDef == self.fromDef and DistanceTags.IntersectionCarInFront or DistanceTags.IntersectionMergingCarInFront
            -- self.driver._nextTag = 'inter: car in front'
            if _needsMinContact and (self._minContact.distance > rd or not self._minContact.active) then
              self._minContact.distance = rd
              self._minContact.refFuturePos = _refFuturePos:clone()
              self._minContact.mainCar = self.guide:getDriver().pos
              self._minContact.nextCar = eDriver.pos
              self._minContact.active = true
            end
          end
        end

      end
    end

    if self.active then

      if not roundaboutFlow and _trajectoryPriority < 0 then
        if _inCurve > 2.501 and rd > 1.5 then
          self._trajectoryPriority = 0
          local newPhase = self.phase - 1
          self.phase = newPhase
          if self.inter.lowestPhase > newPhase then
            self.inter.lowestPhase = newPhase
          end
        else
          -- solves gridlocks that occur when two lower priories get stuck because one with larger weight would
          -- also wait for a car that is blocked by a smaller weight low priority car 
          self._trajectoryOffsetPriority = self._trajectoryOffsetPriority + fromSameSide
        end
      end
    end
    return rd, rc, rt
  end

  return rd, rc, rt
end

function IntersectionManeuver:draw3D(layers)
  if not self.closeToTraverse then return end

  layers:with('Trajectory', true, function()
    local f, t = nil, self.fromDef.fromPos
    for j = 1, 8 do
      f, t = t, self.curveInfo.curve:get((j / 9) * self.curveInfo.curve.length)
      render.debugArrow(f, t, 0.5, self.active and rgbm(0, 3, 0, 1) or rgbm(3, 0, 0, 1))
    end
    render.debugArrow(t, self.toDef.toPos, 0.5, self.active and rgbm(0, 3, 0, 1) or rgbm(3, 0, 0, 1))
  end)

  layers:with('Min contact', true, function()
    _needsMinContact = true
    if self._minContact.mainCar ~= nil then
      render.debugArrow(self._minContact.mainCar, self._minContact.refFuturePos, 0.1, rgbm(0, 3, 0, 1))
      render.debugArrow(self._minContact.mainCar, self._minContact.nextCar, 0.1, rgbm(3, self._minContact.active and 0 or 1, 0, 1))
      render.debugText(self._minContact.mainCar, string.format('CNT: %.2f m', self._minContact.distance),
        rgbm(3, 0.5, 0, 1), 1.5)
      -- self._minContact.mainCar = nil
    end
  end)

  layers:with('Priority', true, function()
    render.debugText(self.guide.driver:getPosRef(), string.format('PRI: %.2f', self._trajectoryPriority))
  end)
end

return class.emmy(IntersectionManeuver, IntersectionManeuver.initialize)
