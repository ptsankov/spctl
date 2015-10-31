R1: Noone can access without a PIN code outside of workhours (time in [8,20])
((and (not pin) (not (time in [8,20]))), (AG (zone in {entry})))

R2: Visitors can access the meeting rooms
((and (role in {visitor}) (time in [8,20])), (EF (zone in {meeting_room})))

R3: Visitors and employees can access the lobby during workhours
((and (role in {visitor hr researcher it}) (time in [8,20])), (EF (zone in {lobby})))

R3: Visitors and employees cannot access the lobby without their pin from midnight outside of workhours
((and (not pin) (not (time in [8,20])) (role in {visitor hr researcher it})), (not (EF (zone in {lobby}))))

R4: Employees can always access the lobby with their PIN
((and pin (role in {hr researcher it})), (EF (zone in {lobby})))

R5: Visitors can access one of the restrooms if they have access to a meeting room
((role in {visitor}), (AG (=> (zone in {meeting_room}) (EF (zone in {restroom})))))

R7: Visitors must pass through the lobby to access the meeting rooms
((role in {visitor}), (not (EU (not (zone in {lobby})) (zone in {meeting_room}))))

R8: Non employees cannot access any office
((role in {visitor postman}), (not (EF (zone in {bureau}))))

R9: Non-HR employees cannot access the staff management office (bur_staff)
((not (role in {hr})), (not (EF (room_id in {bur_staff}))))
HR employees can access the staff management office during (time in [8,20])
((and (time in [8,20]) (role in {hr})), (EF (room_id in {bur_staff})))

R10: The postman and the HR can access the post office during workhours
((and (role in {postman hr}) (time in [8,20])), (EF (zone in {post})))

R11: The postman cannot access the employee corridor (cor1)
((role in {postman}), (not (EF (room_id in {cor1}))))

R12: The postman can access the elevator from the post office
((role in {postman}), (AG (=> post (EF (zone in {elevator})))))

R14: IT and researcher employees cannot access the post office
((not (role in {postman hr})), (not (EF (zone in {post}))))

R15: Only IT can access the server room
((not (role in {it})), (not (EF (zone in {servers}))))
