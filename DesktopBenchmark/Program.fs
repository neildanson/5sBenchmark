
// NOTE: If warnings appear, you may need to retarget this project to .NET 4.0. Show the Solution
// Pad, right-click on the project node, choose 'Options --> Build --> General' and change the target
// framework to .NET 4.0 or .NET 4.5.

module DesktopBenchmark.Main

open System
open System.Collections
open System.Drawing

open System.Threading

open System.Diagnostics


type Vector3D = {X : float; Y : float; Z : float}
    with
    //Addition
    static member (+) (v1, v2) = 
        {X = v1.X + v2.X; Y = v1.Y + v2.Y; Z = v1.Z + v2.Z}

    //Subtraction
    static member (-) (v1, v2) = 
        {X = v1.X - v2.X; Y = v1.Y - v2.Y; Z = v1.Z - v2.Z}

    //Scalar
    static member (*) (v1, l) =
        {X = v1.X * l; Y = v1.Y * l; Z = v1.Z * l}

    static member (/) (v1, l) =
        {X = v1.X / l; Y = v1.Y / l; Z = v1.Z / l}

    //Component
    static member (*) (v1, v2) =
        {X = v1.X * v2.X; Y = v1.Y * v2.Y; Z = v1.Z * v2.Z}    
    
    //Cross product |a||b|sin(theta)
    static member Cross(v1, v2) = 
        {X = v1.Y * v2.Z - v1.Z * v2.Y;
        Y = v1.Z * v2.X - v1.X * v2.Z;
        Z = v1.X * v2.Y - v1.Y * v2.X}

    //Dot product |a||b|cos(theta)
    static member Dot(v1, v2) = 
        (v1.X * v2.X) + (v1.Y * v2.Y) + (v1.Z * v2.Z)
    
    //Normalize the vector
    static member Normalize(v) =
        let mag = Math.Sqrt(Vector3D.Dot(v, v))
        let div = if mag = 0.0 then System.Double.PositiveInfinity else 1.0 /mag
        v * div 

    static member Mag(v) = 
        Math.Sqrt(Vector3D.Dot(v, v))

type Ray = {Position : Vector3D; Direction : Vector3D}

type Color(r:float, g:float, b:float) =
    member __.R = r
    member __.G = g
    member __.B = b
    static member (+) (a:Color , b:Color) = 
        Color(a.R + b.R, a.G + b.G, a.B + b.B)

    static member (-) (a:Color , b:Color) = 
        Color(a.R - b.R, a.G - b.G, a.B - b.B)

    static member (*) (a:Color , b:Color) = 
        Color(a.R * b.R, a.G * b.G, a.B * b.B)

    static member (*) (a:Color , l) = 
        Color(a.R * l, a.G * l, a.B * l)
    
    static member (/) (a:Color , l) = 
        Color(a.R / l, a.G / l, a.B / l)
    
    static member get_Zero() = 
        Color.RGB(0.0,0.0,0.0)

    static member RGB(r, g, b) = 
        Color(r,g,b)

    member this.ToColor() = 
        let legalize (d : float) = if d > 1.0 then 1.0 else d * 255.0
        let r,g,b = (int (legalize this.R), int (legalize this.G), int (legalize this.B))
        let a = 255 <<< 24
        let r = r<<<16
        let g = g<<<8
        let b = b
        a+r+g+b

type Light(pos : Vector3D, col : Color) = 
    member __.Position = pos
    member __.Color = col

type Camera(position:Vector3D, lookAt:Vector3D) = 
    let forward = Vector3D.Normalize(lookAt- position)
    let down = {X = 0.0; Y = -1.0; Z = 0.0}
    let right = Vector3D.Normalize(Vector3D.Cross (forward, down))* 1.5
    let up = Vector3D.Normalize(Vector3D.Cross (forward, right)) * 1.5
    member cam.Position = position
    member cam.Forward = forward
    member cam.Up = up
    member cam.Right = right

type Intersection = { Ray:Ray; Dist:float } 
type Surface =
    {
        Diffuse : Vector3D -> Color;
        Specular : Vector3D -> Color;
        Reflect : Vector3D -> float;
        Roughness : float
    }
    
[<AbstractClass>]
type SceneObject (objectSurface : Surface) =
    member this.Surface = objectSurface 
    abstract Intersects : Ray -> Intersection option
    abstract Normal : Vector3D -> Vector3D

type Sphere(center : Vector3D, radius : float, surface : Surface) = 
    inherit SceneObject(surface)
    member this.Center = center
    member this.Radius = radius

    override this.Intersects (ray : Ray) = 
        let eo = this.Center - ray.Position
        let v = Vector3D.Dot(eo, ray.Direction)
        let getDist = 
            if v < 0.0 then 0.0
            else
                let disc = Math.Pow(radius, 2.0) - (Vector3D.Dot(eo, eo) - Math.Pow(v, 2.0))
                if disc < 0.0 then 0.0 else v - Math.Sqrt(disc)
        let dist = getDist 
        if dist = 0.0 then None else Some({Ray = ray; Dist = dist})

    override this.Normal pos = 
        Vector3D.Normalize(pos- this.Center)

type Plane (normal : Vector3D, offset : float, surface : Surface) = 
    inherit SceneObject(surface)
    member this.Offset = offset
    member this.PlaneNormal = normal
    override this.Intersects ray = 
        let denom = Vector3D.Dot(this.PlaneNormal, ray.Direction)
        if denom > 0.0 then None else Some({Ray = ray; Dist = (Vector3D.Dot(this.PlaneNormal, ray.Position) + this.Offset) / denom })
            
    override this.Normal pos = 
        this.PlaneNormal

type Scene = {
    Lights : Light seq; 
    Objects : SceneObject seq;
    Camera : Camera }

type Raytracer(width, height, scene:Scene) =
    let screenWidth = width
    let screenHeight =height
    let inverseAspectRatio = float height / float width
    let linearScreenBuffer = Array.create (width * height) 0
    
    let fwidth = float width * inverseAspectRatio
    let (halfHeight, halfWidth) = (float height / 2.0, float fwidth / 2.0)
    let (doubleHeight, doubleWidth) = (float height * 2.0, float fwidth * 2.0)


    let intersections ray = 
        let intersections = scene.Objects 
                            |> Seq.choose(fun o -> 
                                let isect = o.Intersects ray
                                match isect with Some(isect) -> Some(o, isect) | None -> None)
        let count = intersections|>Seq.length
        match count with
        | 0 -> None
        | _ -> let obj, isect = intersections|>Seq.minBy(fun (_,isect)-> isect.Dist)
               Some(obj, isect)
                       
    //Get our sorted list of intersections and if theres any data pick that - otherwise return none
    let testRay ray = 
        let intersections = intersections ray
        match intersections with
        | Some(_, isect) -> isect.Dist
        | None -> 0.0
                 
    let getNaturalColor(sceneObject : SceneObject, position, normal, rd) = 
        let computeColorForLight (light : Light) = //async {
            let ldis = light.Position - position
            let livec = Vector3D.Normalize ldis
            let neatIsect = testRay {Position = position; Direction = livec}
            let isInShadow = ((neatIsect > Vector3D.Mag(ldis)) || (neatIsect = 0.0))
            if isInShadow = true then
                let illum = Vector3D.Dot(livec, normal)
                let lcolor = if illum > 0.0 then light.Color * illum else Color.RGB(0.0,0.0,0.0)
                let specular = Vector3D.Dot(livec, Vector3D.Normalize(rd))
                
                let scolor = if specular > 0.0 then light.Color * System.Math.Pow(specular, sceneObject.Surface.Roughness)
                                             else Color.RGB(0.0,0.0,0.0)
                (sceneObject.Surface.Diffuse(position)* lcolor)+(sceneObject.Surface.Specular(position)* scolor)
            else
                Color.RGB(0.0,0.0,0.0)
        //}
                             
        //TODO Parallel - just summing a bunch of colors??
        let finalColor = scene.Lights|>Seq.map (fun light-> computeColorForLight light)|>
                                     //Async.Parallel|>Async.RunSynchronously|>
                                     Seq.sum
        finalColor

        
    let rec traceRay(ray, scene, depth :int) =
        let intersections = intersections ray 
        let intersection = intersections
        if intersection.IsNone then
            Color.RGB(0.0,0.0,0.0)
        else
            let sceneObject, isect = intersection.Value 
            shade(sceneObject, isect, depth)

    and getReflectionColor (sceneObject : SceneObject, pos, norm, rd, depth) = 
           let color = traceRay({ Position = pos; Direction = rd }, scene, depth + 1) 
           color * sceneObject.Surface.Reflect(pos)

    and shade (sceneObject : SceneObject, isect:Intersection, depth) =
        let d = isect.Ray.Direction
        let pos = (isect.Ray.Direction * isect.Dist)+isect.Ray.Position
        let normal = sceneObject.Normal(pos)
        let reflectDir = d - (normal * (Vector3D.Dot(normal, d) * 2.0))
        
        let natural = getNaturalColor(sceneObject, pos, normal, reflectDir)
        if depth>=3 then
            natural + Color.RGB(0.5,0.5,0.5)
        else
            natural + getReflectionColor(sceneObject, pos + (reflectDir * 0.001), normal, reflectDir, depth)
    
    let recenterX (x : int) = 
        let dx = float x 
        (dx - halfWidth) / (doubleWidth)

    let recenterY (y : int) = 
        let dy = float y 
        let height = float height
        -(dy - (halfHeight)) / (doubleHeight)

    let getPoint (x,y, camera:Camera) = 
        Vector3D.Normalize(camera.Forward + ((camera.Right * recenterX(x))+(camera.Up * recenterY(y))))
        
    member this.Render(threaded) = 
        let traceray y = 
            let basex = y*width
            for x in 0..width-1 do 
                let c = basex+x
                linearScreenBuffer.[c]<-traceRay(
                    { Position = scene.Camera.Position; Direction = getPoint(x,y, scene.Camera) },
                     scene, 0).ToColor()

        if threaded then
            let tracerayasync y = async { traceray y }
            
            let result = [|for y in 0..(height - 1) -> tracerayasync y|]|>Async.Parallel|>Async.RunSynchronously
            linearScreenBuffer
        else
            for y in 0..(height - 1) do traceray y
            linearScreenBuffer
    


let someFunction x y = x + y

[<EntryPoint>]
let main args = 
    let Shiny = {
                    Diffuse = fun pos -> Color.RGB(1.0,1.0,1.0)
                    Specular = fun pos -> Color.RGB(0.5, 0.5, 0.5);
                    Reflect = fun pos -> 0.3;
                    Roughness = 50.0
                }
                
    let width = 640    
    let height = 360


    let scene = { Lights = [| Light({ X = 4.0; Y = 3.0; Z= 0.0 }, Color.RGB(0.2 ,0.2, 0.2));
                              Light({ X = 4.0; Y = 5.0; Z= 2.0 }, Color.RGB(0.5 ,0.5, 0.5));  |]; 
                  Objects = [|Sphere( { X = 0.0; Y = 1.0; Z = 5.0}, 1.0,Shiny);
                              Sphere( { X = 2.0; Y = 1.0; Z = 5.0}, 1.0, Shiny);
                              Plane({X = 0.0; Y = 1.0; Z = 0.0}, -1.1, Shiny)  |]; 
                  Camera = Camera( { X = 0.0; Y = 0.0; Z= -3.0 }, { X = 0.0; Y = 0.0; Z = 100.0 }) } 

    let raytracer = Raytracer(width, height, scene)

    let sw = Stopwatch()
    sw.Start()
    let result = raytracer.Render(true)
    sw.Stop()
    Console.WriteLine(String.Format("Elapsed Time {0}", sw.Elapsed))
    0

