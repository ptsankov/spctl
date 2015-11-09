A professor can enter any office assigned to his/her group.
((and (affiliation in {group1}) (role in {faculty})), (EF (and (kind in {office}) (zone in {group1}))))
((and (affiliation in {group2}) (role in {faculty})), (EF (and (kind in {office}) (zone in {group2}))))

Maintenance employees can access the storage room.
((role in {maintenance}), (EF (kind in {storage})))

IT admins can access the server room.
(admin, (EF (kind in {servers})))

Any student can only enter a conference room accompanied by a faculty between 9am and 5pm.
((and student (role in {faculty})), (EF (and (kind in {conf}) (room_id in {r11}))))
((and student (role in {faculty})), (EF (and (kind in {conf}) (room_id in {r12}))))

PhD students can access the offices that belong to their group except the secretary and the professor's office.
((and (affiliation in {group1}) (role in {phd})), (EF (and (kind in {office}) (room_id in {r0}))))
((and (affiliation in {group2}) (role in {phd})), (EF (and (kind in {office}) (and (zone in {group2}) (not (or (secretary in {true}) (faculty in {true})))))))
((and (affiliation in {group2}) (role in {phd})), (EF (and (kind in {office}) (room_id in {r34}))))

PhD students cannot access their group's secretary and professor office.
((role in {phd}), (AG (not (secretary in {true}))))
((role in {phd}), (AG (not (faculty in {true}))))

Teaching rooms can be freely accessed by anyone between 8AM and 8PM
((time in [8,20]), (EF (room_id in {r13})))

Only phd students and professors can access teaching rooms between 8PM and 8AM
((and (not (time in [8, 20])) (role in {phd faculty})), (EF (room_id in {r13})))

Only phd students and professors can access teaching rooms between 8PM and 8AM
((and (not (time in [8,20])) (role in {bot})), (AG (not (room_id in {r13}))))
