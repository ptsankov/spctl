No passengers can access non-public areas without a boarding pass
((and (role in {passenger}) (boardingpass in {bot})), (not (EF (not (zone in {public})))))

Staff can access the duty free shops
((role in {staff}), (EF (shops in {true})))

Only staff can access the elevators
((not (role in {staff})), (not (EF (elevators in {true}))))

Staff can access the elevators
((role in {staff}), (EF (elevators in {true})))
((role in {staff}), (EF (room_id in {elev1})))
((role in {staff}), (EF (room_id in {elev2})))

In case of a security breach noone can access the duty-free shops

Economy passengers cannot access through the priority gate
((and (role in {passenger}) (boardingpass in {economy})), (not (EF (business in {true}))))

Economy passengers with boarding passes can reach the secured area
((and (role in {passenger}) (not (boardingpass in {bot}))), (EF (zone in {secured})))

Priority passengers can access through both the economy and the priority gates
((and (role in {passenger}) (boardingpass in {priority})), (EF (business in {true})))

Passengers with boarding passes can access the duty-free shop
((and (role in {passenger}) (not (boardingpass in {bot}))), (EF (shops in {true})))

Only staff can pass thorugh the designated screening security check
((and (role in {staff}) (not (boardingpass in {bot}))), (EF (shops in {true})))

All passengers with boarding passes can access through all security checks (except the one for staff)
((and (role in {passenger}) (not (boardingpass in {bot}))), (EF (room_id in {sec2})))
((and (role in {passenger}) (not (boardingpass in {bot}))), (EF (room_id in {sec3})))
((and (role in {passenger}) (not (boardingpass in {bot}))), (EF (room_id in {sec4})))

Passengers cannot access the secured area without first passing through security checks
((role in {passenger}), (not (EU (not (room_id in {sec2 sec3 sec4})) (zone in {secured}))))