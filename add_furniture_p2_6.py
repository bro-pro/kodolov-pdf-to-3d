import json, sys, math
from pathlib import Path
import trimesh
from shapely.geometry import Polygon, box, Point
from shapely.affinity import rotate, translate

src=Path(sys.argv[1])
out=Path(sys.argv[2])
d=json.loads(src.read_text(encoding='utf-8'))
scene=trimesh.load(sys.argv[3], force='scene')

# Use room geometry only; furniture is explicitly heuristic and non-semantic.
rooms={r['id']: Polygon(r['polygon_m']) for r in d.get('rooms',[])}
used={rid:[] for rid in rooms}

# (name, room, width, depth, height, preferred point, rotation)
items=[
 ('sofa','room_001',2.20,0.90,0.85,(4.0,5.9),0),
 ('coffee_table','room_001',1.10,0.60,0.42,(4.0,4.6),0),
 ('kitchen_counter','room_001',3.00,0.60,0.90,(2.2,0.65),0),
 ('dining_table','room_001',1.40,0.80,0.75,(5.9,5.0),0),
 ('bed','room_002',1.60,2.00,0.55,(10.8,5.6),0),
 ('wardrobe','room_002',0.60,2.00,2.20,(12.0,5.7),0),
 ('dining_chair_1','room_001',0.45,0.45,0.85,(5.0,5.0),0),
 ('dining_chair_2','room_001',0.45,0.45,0.85,(6.8,5.0),0),
 ('cabinet','room_003',0.45,1.60,2.20,(2.4,8.9),90),
 ('bath_shower','room_004',0.90,0.90,2.10,(10.4,1.6),0),
 ('bath_sink','room_004',0.55,0.45,0.85,(11.4,2.0),0),
 ('bath_toilet','room_004',0.40,0.65,0.45,(11.5,1.1),0),
 ('storage','room_005',0.55,1.30,2.20,(7.3,1.7),90),
 ('entry_console','room_006',0.40,1.00,0.80,(5.8,1.7),90),
]

def footprint(w,d,x,y,ang):
    p=box(-w/2,-d/2,w/2,d/2)
    p=rotate(p,ang,origin=(0,0),use_radians=False)
    return translate(p,xoff=x,yoff=y)

def add_box(name,w,d,h,x,y,z=0,ang=0):
    m=trimesh.creation.box(extents=[w,d,h])
    m.apply_translation([x,y,z+h/2])
    if ang:
        # rotate around vertical axis at object center
        m.apply_transform(trimesh.transformations.rotation_matrix(math.radians(ang),[0,0,1],[x,y,0]))
    scene.add_geometry(m, node_name='furniture_'+name, geom_name='furniture_'+name)

placed=[]
for name,rid,w,dep,h,pref,ang in items:
    if rid not in rooms: continue
    poly=rooms[rid]
    candidates=[]
    px,py=pref
    # Search around preferred point, then whole room grid if needed.
    for radius in [0,0.3,0.6,0.9,1.2,1.6,2.0]:
        for k in range(24):
            a=2*math.pi*k/24
            x=px+radius*math.cos(a); y=py+radius*math.sin(a)
            fp=footprint(w,dep,x,y,ang)
            if not poly.buffer(-0.06).contains(fp): continue
            if any(fp.intersects(q.buffer(0.05)) for q in used[rid]): continue
            # Keep distance from doors/windows; openings on room boundary.
            score=poly.centroid.distance(Point(x,y))
            candidates.append((score,x,y,fp))
        if candidates: break
    if not candidates:
        continue
    _,x,y,fp=min(candidates,key=lambda t:t[0])
    used[rid].append(fp)
    add_box(name,w,dep,h,x,y,ang=ang)
    placed.append({'id':'furniture_'+name,'type':name,'room_id':rid,'width_m':w,'depth_m':dep,'height_m':h,'x_m':round(x,3),'y_m':round(y,3),'rotation_deg':ang,'source':'heuristic'})

d2=d.copy()
d2['schema']='kodolov.project.v0.6'
d2['furniture']={'status':'heuristic_placement','count':len(placed),'objects':placed,'note':'Типовые объекты расставлены эвристически по геометрии помещений; семантика помещений не подтверждена.'}
scene.export(out)
jsonout=out.with_suffix('.json')
jsonout.write_text(json.dumps(d2,ensure_ascii=False,indent=2),encoding='utf-8')
print('placed',len(placed))
for x in placed: print(x)
print('saved',out)
print('json',jsonout)
