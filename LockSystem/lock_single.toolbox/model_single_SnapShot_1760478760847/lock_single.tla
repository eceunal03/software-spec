---------------------------- MODULE lock_single ----------------------------

EXTENDS lock_data


(* --algorithm lock_system

\*****************************
\* Define global variables
\*****************************
variables
  \* Variables for locks
  lockOrientation = "west_low",
  doorsOpen = [ls \in LockSide |-> FALSE],
  valvesOpen = [vs \in ValveSide |-> FALSE],
  waterLevel = "low",
  
  \* Variables for single ship
  shipLocation = 0,
  shipStatus = "go_to_east",
  
  \* Command for lock
  \* for command "change_door" the side should be "west" or "east"
  \* for command "change_valve" the side should be "high" or "low"
  lockCommand = [command |-> "finished", open |-> FALSE, side |-> "west"],
  \* Central requests of all ships
  requests = << >>,
  \* Permissions per ship
  permissions = << >>;

define

\*****************************
\* Helper functions
\*****************************
\* Check if ship is within the lock
InLock == IsLock(shipLocation)


\*****************************
\* Type checks
\*****************************
\* Check that variables use the correct type
TypeOK == /\ lockOrientation \in LockOrientation
          /\ \A ls \in LockSide : doorsOpen[ls] \in BOOLEAN
          /\ \A vs \in ValveSide : valvesOpen[vs] \in BOOLEAN
          /\ waterLevel \in WaterLevel
          /\ lockCommand.command \in LockCommand
          /\ lockCommand.open \in BOOLEAN
          /\ lockCommand.side \in LockSide \union ValveSide
          /\ shipLocation \in Locations
          /\ shipStatus \in ShipStatus
          /\ \A i \in 1..Len(permissions):
               /\ permissions[i].lock \in Locks
               /\ permissions[i].granted \in BOOLEAN
          /\ \A i \in 1..Len(requests):
               /\ requests[i].ship \in Ships
               /\ requests[i].lock \in Locks
               /\ requests[i].side \in LockSide

\* Check that message queues are not overflowing
MessagesOK == /\ Len(requests) <= 1
              /\ Len(permissions) <= 1


\*****************************
\* Requirements on lock
\*****************************
\* The eastern and western doors are never simultaneously open.
DoorsMutex ==
    ~(doorsOpen["west"] /\ doorsOpen["east"])

\* When one pair of doors is open, the opposite valve is closed.
DoorsOpenValvesClosed ==
    (doorsOpen["west"] => ~valvesOpen["high"]) /\
    (doorsOpen["east"] => ~valvesOpen["low"])

\* Doors correspond to correct water levels.
DoorsOpenWaterlevelRight ==
    (doorsOpen["west"] => waterLevel = "low") /\
    (doorsOpen["east"] => waterLevel = "high")

\* --- Liveness properties ---
\* Every request will eventually be granted (lock entered).
RequestLockFulfilled ==
    \A ship \in Ships :
        (<>[](InLock => TRUE))

\* Water level changes infinitely often between low and high.
WaterlevelChange ==
    [](<>(waterLevel = "low")) /\ [](<>(waterLevel = "high"))

\* Ships keep making requests infinitely often.
RequestsShips ==
    [](<>(Len(requests) > 0))

\* Ships reach their goal locations infinitely often.
ShipsReachGoals ==
    [](<>(shipStatus = "goal_reached"))


end define;


\*****************************
\* Helper macros
\*****************************

\* Update the water level according to the state of doors and valves
macro updateWaterLevel(lock_orientation, doors, valves, waterlevel) begin
  if valves["low"] then
      \* Water can flow out through valve
      waterlevel := "low";
  elsif (lock_orientation = "west_low" /\ doors["west"])
         \/ (lock_orientation = "east_low" /\ doors["east"]) then
      \* Water can flow out through lower door
      waterlevel := "low";
  elsif valves["high"] then
      \* Water can flow in through valve
      waterlevel := "high";
  elsif (lock_orientation = "west_low" /\ doors["east"])
         \/ (lock_orientation = "east_low" /\ doors["west"]) then
      \* Water can flow in through higher door
      waterlevel := "high";
  \* In other case, the water level stays the same
  end if;
end macro

\* Read res from queue.
\* The macro awaits a non-empty queue.
macro read(queue, res) begin
  await queue /= <<>>;
  res := Head(queue);
  queue := Tail(queue);
end macro

\* Write msg to the queue.
macro write(queue, msg) begin
  queue := Append(queue, msg);
end macro


\*****************************
\* Process for a lock
\*****************************
process lockProcess \in Locks
begin
  LockWaitForCommand:
    while TRUE do
      await lockCommand.command /= "finished";
      if lockCommand.command = "change_door" then
        \* Change status of door
        doorsOpen[lockCommand.side] := lockCommand.open;
      elsif lockCommand.command = "change_valve" then
        \* Change status of valve
        valvesOpen[lockCommand.side] := lockCommand.open;
      else
        \* should not happen
        assert FALSE;
      end if;
  LockUpdateWaterLevel:
      updateWaterLevel(lockOrientation, doorsOpen, valvesOpen, waterLevel);
  LockCommandFinished:
      lockCommand.command := "finished";    
    end while;
end process;


\*****************************
\* Process for a ship
\*****************************
process shipProcess \in Ships
variables
  perm = [lock |-> 1, granted |-> FALSE]
begin
  ShipNextIteration:
    while TRUE do
      if shipStatus = "go_to_east" then
        if shipLocation = EastEnd then
  ShipGoalReachedEast:
          shipStatus := "goal_reached";
        else
          if ~InLock then
  ShipRequestWest:
            \* Request west doors of lock
            write(requests, [ship |-> self, lock |-> 1, side |-> "west"]);
  ShipWaitForWest:
            \* Wait for permission
            read(permissions, perm);
            assert perm.lock = GetLock(shipLocation+1);
          else
  ShipRequestEastInLock:
            \* Request east doors of lock
            write(requests, [ship |-> self, lock |-> 1, side |-> "east"]);
  ShipWaitForEastInLock:
            \* Wait for permission
            read(permissions, perm);
            assert perm.lock = GetLock(shipLocation);
          end if;
  ShipMoveEast:
          if perm.granted then
            \* Move ship
            assert doorsOpen[IF InLock THEN "east" ELSE "west"];
            shipLocation := shipLocation + 1;
          end if;
        end if;
      elsif shipStatus = "go_to_west" then
        if shipLocation = WestEnd then
  ShipGoalReachedWest:
          shipStatus := "goal_reached";
        else
          if ~InLock then
  ShipRequestEast:
            \* Request east doors of lock
            write(requests, [ship |-> self, lock |-> 1, side |-> "east"]);
  ShipWaitForEast:
            \* Wait for permission
            read(permissions, perm);
            assert perm.lock = GetLock(shipLocation-1);
          else
  ShipRequestWestInLock:
            \* Request west doors of lock
            write(requests, [ship |-> self, lock |-> 1, side |-> "west"]);
  ShipWaitForWestInLock:
            \* Wait for permission
            read(permissions, perm);
            assert perm.lock = GetLock(shipLocation);
          end if;
  ShipMoveWest:
          if perm.granted then
            \* Move ship
            assert doorsOpen[IF InLock THEN "west" ELSE "east"];
            shipLocation := shipLocation - 1;
          end if;
        end if;
      else
        assert shipStatus = "goal_reached";
  ShipTurnAround:
        \* Turn around
        shipStatus := IF shipLocation = WestEnd THEN "go_to_east" ELSE "go_to_west";
      end if;
    end while;
end process;


\*****************************
\* Process for the controller
\*****************************
process controlProcess = 0
variable req;
begin
  ControlLoop:
  while TRUE do

    WaitForRequest:
      read(requests, req);

    CheckSafety:
      if ~InLock then

        PrepareLock:
          if (lockOrientation = "west_low" /\ req.side = "west")
             \/ (lockOrientation = "east_low" /\ req.side = "east") then

            \* --- Handle low-side entry ---
            SetLowValve:
              lockCommand := [command |-> "change_valve", open |-> TRUE, side |-> "low"];
              await lockCommand.command = "finished";

            \* --- Open the low door only if no other door is open ---
            OpenLowDoor:
              if ~(doorsOpen["west"] \/ doorsOpen["east"]) then
                lockCommand := [command |-> "change_door", open |-> TRUE, side |-> req.side];
                await lockCommand.command = "finished";
              end if;

          else

            \* --- Handle high-side entry ---
            SetHighValve:
              lockCommand := [command |-> "change_valve", open |-> TRUE, side |-> "high"];
              await lockCommand.command = "finished";

            \* --- Open the high door only if no other door is open ---
            OpenHighDoor:
              if ~(doorsOpen["west"] \/ doorsOpen["east"]) then
                lockCommand := [command |-> "change_door", open |-> TRUE, side |-> req.side];
                await lockCommand.command = "finished";
              end if;
          end if;

        \* --- Grant ship permission and close doors/valves safely ---
        GrantPermission:
          write(permissions, [lock |-> req.lock, granted |-> TRUE]);

        CloseDoor:
          lockCommand := [command |-> "change_door", open |-> FALSE, side |-> req.side];
          await lockCommand.command = "finished";

        CloseValvesLow:
          lockCommand := [command |-> "change_valve", open |-> FALSE, side |-> "low"];
          await lockCommand.command = "finished";

        CloseValvesHigh:
          lockCommand := [command |-> "change_valve", open |-> FALSE, side |-> "high"];
          await lockCommand.command = "finished";

      else
        \* --- Deny if unsafe or already inside ---
        DenyRequest:
          write(permissions, [lock |-> req.lock, granted |-> FALSE]);
      end if;
      Idle:
        skip;
  end while;
  
end process;





end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "d7ff495e" /\ chksum(tla) = "75d8ba52")
CONSTANT defaultInitValue
VARIABLES lockOrientation, doorsOpen, valvesOpen, waterLevel, shipLocation, 
          shipStatus, lockCommand, requests, permissions, pc

(* define statement *)
InLock == IsLock(shipLocation)






TypeOK == /\ lockOrientation \in LockOrientation
          /\ \A ls \in LockSide : doorsOpen[ls] \in BOOLEAN
          /\ \A vs \in ValveSide : valvesOpen[vs] \in BOOLEAN
          /\ waterLevel \in WaterLevel
          /\ lockCommand.command \in LockCommand
          /\ lockCommand.open \in BOOLEAN
          /\ lockCommand.side \in LockSide \union ValveSide
          /\ shipLocation \in Locations
          /\ shipStatus \in ShipStatus
          /\ \A i \in 1..Len(permissions):
               /\ permissions[i].lock \in Locks
               /\ permissions[i].granted \in BOOLEAN
          /\ \A i \in 1..Len(requests):
               /\ requests[i].ship \in Ships
               /\ requests[i].lock \in Locks
               /\ requests[i].side \in LockSide


MessagesOK == /\ Len(requests) <= 1
              /\ Len(permissions) <= 1






DoorsMutex ==
    ~(doorsOpen["west"] /\ doorsOpen["east"])


DoorsOpenValvesClosed ==
    (doorsOpen["west"] => ~valvesOpen["high"]) /\
    (doorsOpen["east"] => ~valvesOpen["low"])


DoorsOpenWaterlevelRight ==
    (doorsOpen["west"] => waterLevel = "low") /\
    (doorsOpen["east"] => waterLevel = "high")



RequestLockFulfilled ==
    \A ship \in Ships :
        (<>[](InLock => TRUE))


WaterlevelChange ==
    [](<>(waterLevel = "low")) /\ [](<>(waterLevel = "high"))


RequestsShips ==
    [](<>(Len(requests) > 0))


ShipsReachGoals ==
    [](<>(shipStatus = "goal_reached"))

VARIABLES perm, req

vars == << lockOrientation, doorsOpen, valvesOpen, waterLevel, shipLocation, 
           shipStatus, lockCommand, requests, permissions, pc, perm, req >>

ProcSet == (Locks) \cup (Ships) \cup {0}

Init == (* Global variables *)
        /\ lockOrientation = "west_low"
        /\ doorsOpen = [ls \in LockSide |-> FALSE]
        /\ valvesOpen = [vs \in ValveSide |-> FALSE]
        /\ waterLevel = "low"
        /\ shipLocation = 0
        /\ shipStatus = "go_to_east"
        /\ lockCommand = [command |-> "finished", open |-> FALSE, side |-> "west"]
        /\ requests = << >>
        /\ permissions = << >>
        (* Process shipProcess *)
        /\ perm = [self \in Ships |-> [lock |-> 1, granted |-> FALSE]]
        (* Process controlProcess *)
        /\ req = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self \in Locks -> "LockWaitForCommand"
                                        [] self \in Ships -> "ShipNextIteration"
                                        [] self = 0 -> "ControlLoop"]

LockWaitForCommand(self) == /\ pc[self] = "LockWaitForCommand"
                            /\ lockCommand.command /= "finished"
                            /\ IF lockCommand.command = "change_door"
                                  THEN /\ doorsOpen' = [doorsOpen EXCEPT ![lockCommand.side] = lockCommand.open]
                                       /\ UNCHANGED valvesOpen
                                  ELSE /\ IF lockCommand.command = "change_valve"
                                             THEN /\ valvesOpen' = [valvesOpen EXCEPT ![lockCommand.side] = lockCommand.open]
                                             ELSE /\ Assert(FALSE, 
                                                            "Failure of assertion at line 159, column 9.")
                                                  /\ UNCHANGED valvesOpen
                                       /\ UNCHANGED doorsOpen
                            /\ pc' = [pc EXCEPT ![self] = "LockUpdateWaterLevel"]
                            /\ UNCHANGED << lockOrientation, waterLevel, 
                                            shipLocation, shipStatus, 
                                            lockCommand, requests, permissions, 
                                            perm, req >>

LockUpdateWaterLevel(self) == /\ pc[self] = "LockUpdateWaterLevel"
                              /\ IF valvesOpen["low"]
                                    THEN /\ waterLevel' = "low"
                                    ELSE /\ IF (lockOrientation = "west_low" /\ doorsOpen["west"])
                                                \/ (lockOrientation = "east_low" /\ doorsOpen["east"])
                                               THEN /\ waterLevel' = "low"
                                               ELSE /\ IF valvesOpen["high"]
                                                          THEN /\ waterLevel' = "high"
                                                          ELSE /\ IF (lockOrientation = "west_low" /\ doorsOpen["east"])
                                                                      \/ (lockOrientation = "east_low" /\ doorsOpen["west"])
                                                                     THEN /\ waterLevel' = "high"
                                                                     ELSE /\ TRUE
                                                                          /\ UNCHANGED waterLevel
                              /\ pc' = [pc EXCEPT ![self] = "LockCommandFinished"]
                              /\ UNCHANGED << lockOrientation, doorsOpen, 
                                              valvesOpen, shipLocation, 
                                              shipStatus, lockCommand, 
                                              requests, permissions, perm, req >>

LockCommandFinished(self) == /\ pc[self] = "LockCommandFinished"
                             /\ lockCommand' = [lockCommand EXCEPT !.command = "finished"]
                             /\ pc' = [pc EXCEPT ![self] = "LockWaitForCommand"]
                             /\ UNCHANGED << lockOrientation, doorsOpen, 
                                             valvesOpen, waterLevel, 
                                             shipLocation, shipStatus, 
                                             requests, permissions, perm, req >>

lockProcess(self) == LockWaitForCommand(self) \/ LockUpdateWaterLevel(self)
                        \/ LockCommandFinished(self)

ShipNextIteration(self) == /\ pc[self] = "ShipNextIteration"
                           /\ IF shipStatus = "go_to_east"
                                 THEN /\ IF shipLocation = EastEnd
                                            THEN /\ pc' = [pc EXCEPT ![self] = "ShipGoalReachedEast"]
                                            ELSE /\ IF ~InLock
                                                       THEN /\ pc' = [pc EXCEPT ![self] = "ShipRequestWest"]
                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "ShipRequestEastInLock"]
                                 ELSE /\ IF shipStatus = "go_to_west"
                                            THEN /\ IF shipLocation = WestEnd
                                                       THEN /\ pc' = [pc EXCEPT ![self] = "ShipGoalReachedWest"]
                                                       ELSE /\ IF ~InLock
                                                                  THEN /\ pc' = [pc EXCEPT ![self] = "ShipRequestEast"]
                                                                  ELSE /\ pc' = [pc EXCEPT ![self] = "ShipRequestWestInLock"]
                                            ELSE /\ Assert(shipStatus = "goal_reached", 
                                                           "Failure of assertion at line 237, column 9.")
                                                 /\ pc' = [pc EXCEPT ![self] = "ShipTurnAround"]
                           /\ UNCHANGED << lockOrientation, doorsOpen, 
                                           valvesOpen, waterLevel, 
                                           shipLocation, shipStatus, 
                                           lockCommand, requests, permissions, 
                                           perm, req >>

ShipGoalReachedEast(self) == /\ pc[self] = "ShipGoalReachedEast"
                             /\ shipStatus' = "goal_reached"
                             /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                             /\ UNCHANGED << lockOrientation, doorsOpen, 
                                             valvesOpen, waterLevel, 
                                             shipLocation, lockCommand, 
                                             requests, permissions, perm, req >>

ShipMoveEast(self) == /\ pc[self] = "ShipMoveEast"
                      /\ IF perm[self].granted
                            THEN /\ Assert(doorsOpen[IF InLock THEN "east" ELSE "west"], 
                                           "Failure of assertion at line 203, column 13.")
                                 /\ shipLocation' = shipLocation + 1
                            ELSE /\ TRUE
                                 /\ UNCHANGED shipLocation
                      /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                      /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                      waterLevel, shipStatus, lockCommand, 
                                      requests, permissions, perm, req >>

ShipRequestWest(self) == /\ pc[self] = "ShipRequestWest"
                         /\ requests' = Append(requests, ([ship |-> self, lock |-> 1, side |-> "west"]))
                         /\ pc' = [pc EXCEPT ![self] = "ShipWaitForWest"]
                         /\ UNCHANGED << lockOrientation, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocation, 
                                         shipStatus, lockCommand, permissions, 
                                         perm, req >>

ShipWaitForWest(self) == /\ pc[self] = "ShipWaitForWest"
                         /\ permissions /= <<>>
                         /\ perm' = [perm EXCEPT ![self] = Head(permissions)]
                         /\ permissions' = Tail(permissions)
                         /\ Assert(perm'[self].lock = GetLock(shipLocation+1), 
                                   "Failure of assertion at line 190, column 13.")
                         /\ pc' = [pc EXCEPT ![self] = "ShipMoveEast"]
                         /\ UNCHANGED << lockOrientation, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocation, 
                                         shipStatus, lockCommand, requests, 
                                         req >>

ShipRequestEastInLock(self) == /\ pc[self] = "ShipRequestEastInLock"
                               /\ requests' = Append(requests, ([ship |-> self, lock |-> 1, side |-> "east"]))
                               /\ pc' = [pc EXCEPT ![self] = "ShipWaitForEastInLock"]
                               /\ UNCHANGED << lockOrientation, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocation, shipStatus, 
                                               lockCommand, permissions, perm, 
                                               req >>

ShipWaitForEastInLock(self) == /\ pc[self] = "ShipWaitForEastInLock"
                               /\ permissions /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head(permissions)]
                               /\ permissions' = Tail(permissions)
                               /\ Assert(perm'[self].lock = GetLock(shipLocation), 
                                         "Failure of assertion at line 198, column 13.")
                               /\ pc' = [pc EXCEPT ![self] = "ShipMoveEast"]
                               /\ UNCHANGED << lockOrientation, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocation, shipStatus, 
                                               lockCommand, requests, req >>

ShipTurnAround(self) == /\ pc[self] = "ShipTurnAround"
                        /\ shipStatus' = (IF shipLocation = WestEnd THEN "go_to_east" ELSE "go_to_west")
                        /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                        /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                        waterLevel, shipLocation, lockCommand, 
                                        requests, permissions, perm, req >>

ShipGoalReachedWest(self) == /\ pc[self] = "ShipGoalReachedWest"
                             /\ shipStatus' = "goal_reached"
                             /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                             /\ UNCHANGED << lockOrientation, doorsOpen, 
                                             valvesOpen, waterLevel, 
                                             shipLocation, lockCommand, 
                                             requests, permissions, perm, req >>

ShipMoveWest(self) == /\ pc[self] = "ShipMoveWest"
                      /\ IF perm[self].granted
                            THEN /\ Assert(doorsOpen[IF InLock THEN "west" ELSE "east"], 
                                           "Failure of assertion at line 232, column 13.")
                                 /\ shipLocation' = shipLocation - 1
                            ELSE /\ TRUE
                                 /\ UNCHANGED shipLocation
                      /\ pc' = [pc EXCEPT ![self] = "ShipNextIteration"]
                      /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                      waterLevel, shipStatus, lockCommand, 
                                      requests, permissions, perm, req >>

ShipRequestEast(self) == /\ pc[self] = "ShipRequestEast"
                         /\ requests' = Append(requests, ([ship |-> self, lock |-> 1, side |-> "east"]))
                         /\ pc' = [pc EXCEPT ![self] = "ShipWaitForEast"]
                         /\ UNCHANGED << lockOrientation, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocation, 
                                         shipStatus, lockCommand, permissions, 
                                         perm, req >>

ShipWaitForEast(self) == /\ pc[self] = "ShipWaitForEast"
                         /\ permissions /= <<>>
                         /\ perm' = [perm EXCEPT ![self] = Head(permissions)]
                         /\ permissions' = Tail(permissions)
                         /\ Assert(perm'[self].lock = GetLock(shipLocation-1), 
                                   "Failure of assertion at line 219, column 13.")
                         /\ pc' = [pc EXCEPT ![self] = "ShipMoveWest"]
                         /\ UNCHANGED << lockOrientation, doorsOpen, 
                                         valvesOpen, waterLevel, shipLocation, 
                                         shipStatus, lockCommand, requests, 
                                         req >>

ShipRequestWestInLock(self) == /\ pc[self] = "ShipRequestWestInLock"
                               /\ requests' = Append(requests, ([ship |-> self, lock |-> 1, side |-> "west"]))
                               /\ pc' = [pc EXCEPT ![self] = "ShipWaitForWestInLock"]
                               /\ UNCHANGED << lockOrientation, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocation, shipStatus, 
                                               lockCommand, permissions, perm, 
                                               req >>

ShipWaitForWestInLock(self) == /\ pc[self] = "ShipWaitForWestInLock"
                               /\ permissions /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head(permissions)]
                               /\ permissions' = Tail(permissions)
                               /\ Assert(perm'[self].lock = GetLock(shipLocation), 
                                         "Failure of assertion at line 227, column 13.")
                               /\ pc' = [pc EXCEPT ![self] = "ShipMoveWest"]
                               /\ UNCHANGED << lockOrientation, doorsOpen, 
                                               valvesOpen, waterLevel, 
                                               shipLocation, shipStatus, 
                                               lockCommand, requests, req >>

shipProcess(self) == ShipNextIteration(self) \/ ShipGoalReachedEast(self)
                        \/ ShipMoveEast(self) \/ ShipRequestWest(self)
                        \/ ShipWaitForWest(self)
                        \/ ShipRequestEastInLock(self)
                        \/ ShipWaitForEastInLock(self)
                        \/ ShipTurnAround(self)
                        \/ ShipGoalReachedWest(self) \/ ShipMoveWest(self)
                        \/ ShipRequestEast(self) \/ ShipWaitForEast(self)
                        \/ ShipRequestWestInLock(self)
                        \/ ShipWaitForWestInLock(self)

ControlLoop == /\ pc[0] = "ControlLoop"
               /\ pc' = [pc EXCEPT ![0] = "WaitForRequest"]
               /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                               waterLevel, shipLocation, shipStatus, 
                               lockCommand, requests, permissions, perm, req >>

WaitForRequest == /\ pc[0] = "WaitForRequest"
                  /\ requests /= <<>>
                  /\ req' = Head(requests)
                  /\ requests' = Tail(requests)
                  /\ pc' = [pc EXCEPT ![0] = "CheckSafety"]
                  /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                  waterLevel, shipLocation, shipStatus, 
                                  lockCommand, permissions, perm >>

CheckSafety == /\ pc[0] = "CheckSafety"
               /\ IF ~InLock
                     THEN /\ pc' = [pc EXCEPT ![0] = "PrepareLock"]
                     ELSE /\ pc' = [pc EXCEPT ![0] = "DenyRequest"]
               /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                               waterLevel, shipLocation, shipStatus, 
                               lockCommand, requests, permissions, perm, req >>

PrepareLock == /\ pc[0] = "PrepareLock"
               /\ IF (lockOrientation = "west_low" /\ req.side = "west")
                     \/ (lockOrientation = "east_low" /\ req.side = "east")
                     THEN /\ pc' = [pc EXCEPT ![0] = "SetLowValve"]
                     ELSE /\ pc' = [pc EXCEPT ![0] = "SetHighValve"]
               /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                               waterLevel, shipLocation, shipStatus, 
                               lockCommand, requests, permissions, perm, req >>

SetLowValve == /\ pc[0] = "SetLowValve"
               /\ lockCommand' = [command |-> "change_valve", open |-> TRUE, side |-> "low"]
               /\ lockCommand'.command = "finished"
               /\ pc' = [pc EXCEPT ![0] = "OpenLowDoor"]
               /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                               waterLevel, shipLocation, shipStatus, requests, 
                               permissions, perm, req >>

OpenLowDoor == /\ pc[0] = "OpenLowDoor"
               /\ IF ~(doorsOpen["west"] \/ doorsOpen["east"])
                     THEN /\ lockCommand' = [command |-> "change_door", open |-> TRUE, side |-> req.side]
                          /\ lockCommand'.command = "finished"
                     ELSE /\ TRUE
                          /\ UNCHANGED lockCommand
               /\ pc' = [pc EXCEPT ![0] = "GrantPermission"]
               /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                               waterLevel, shipLocation, shipStatus, requests, 
                               permissions, perm, req >>

SetHighValve == /\ pc[0] = "SetHighValve"
                /\ lockCommand' = [command |-> "change_valve", open |-> TRUE, side |-> "high"]
                /\ lockCommand'.command = "finished"
                /\ pc' = [pc EXCEPT ![0] = "OpenHighDoor"]
                /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                waterLevel, shipLocation, shipStatus, requests, 
                                permissions, perm, req >>

OpenHighDoor == /\ pc[0] = "OpenHighDoor"
                /\ IF ~(doorsOpen["west"] \/ doorsOpen["east"])
                      THEN /\ lockCommand' = [command |-> "change_door", open |-> TRUE, side |-> req.side]
                           /\ lockCommand'.command = "finished"
                      ELSE /\ TRUE
                           /\ UNCHANGED lockCommand
                /\ pc' = [pc EXCEPT ![0] = "GrantPermission"]
                /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                waterLevel, shipLocation, shipStatus, requests, 
                                permissions, perm, req >>

GrantPermission == /\ pc[0] = "GrantPermission"
                   /\ permissions' = Append(permissions, ([lock |-> req.lock, granted |-> TRUE]))
                   /\ pc' = [pc EXCEPT ![0] = "CloseDoor"]
                   /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                   waterLevel, shipLocation, shipStatus, 
                                   lockCommand, requests, perm, req >>

CloseDoor == /\ pc[0] = "CloseDoor"
             /\ lockCommand' = [command |-> "change_door", open |-> FALSE, side |-> req.side]
             /\ lockCommand'.command = "finished"
             /\ pc' = [pc EXCEPT ![0] = "CloseValvesLow"]
             /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                             waterLevel, shipLocation, shipStatus, requests, 
                             permissions, perm, req >>

CloseValvesLow == /\ pc[0] = "CloseValvesLow"
                  /\ lockCommand' = [command |-> "change_valve", open |-> FALSE, side |-> "low"]
                  /\ lockCommand'.command = "finished"
                  /\ pc' = [pc EXCEPT ![0] = "CloseValvesHigh"]
                  /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                  waterLevel, shipLocation, shipStatus, 
                                  requests, permissions, perm, req >>

CloseValvesHigh == /\ pc[0] = "CloseValvesHigh"
                   /\ lockCommand' = [command |-> "change_valve", open |-> FALSE, side |-> "high"]
                   /\ lockCommand'.command = "finished"
                   /\ pc' = [pc EXCEPT ![0] = "Idle"]
                   /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                                   waterLevel, shipLocation, shipStatus, 
                                   requests, permissions, perm, req >>

DenyRequest == /\ pc[0] = "DenyRequest"
               /\ permissions' = Append(permissions, ([lock |-> req.lock, granted |-> FALSE]))
               /\ pc' = [pc EXCEPT ![0] = "Idle"]
               /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, 
                               waterLevel, shipLocation, shipStatus, 
                               lockCommand, requests, perm, req >>

Idle == /\ pc[0] = "Idle"
        /\ TRUE
        /\ pc' = [pc EXCEPT ![0] = "ControlLoop"]
        /\ UNCHANGED << lockOrientation, doorsOpen, valvesOpen, waterLevel, 
                        shipLocation, shipStatus, lockCommand, requests, 
                        permissions, perm, req >>

controlProcess == ControlLoop \/ WaitForRequest \/ CheckSafety
                     \/ PrepareLock \/ SetLowValve \/ OpenLowDoor
                     \/ SetHighValve \/ OpenHighDoor \/ GrantPermission
                     \/ CloseDoor \/ CloseValvesLow \/ CloseValvesHigh
                     \/ DenyRequest \/ Idle

Next == controlProcess
           \/ (\E self \in Locks: lockProcess(self))
           \/ (\E self \in Ships: shipProcess(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 



=============================================================================
\* Modification History
\* Last modified Tue Oct 14 23:52:34 CEST 2025 by 20241799
\* Last modified Tue Oct 14 22:48:23 CEST 2025 by 20241799
\* Last modified Wed Sep 24 11:08:53 CEST 2025 by mvolk
\* Created Thu Aug 28 11:30:23 CEST 2025 by mvolk
