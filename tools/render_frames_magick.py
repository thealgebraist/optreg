import os

def render_frames():
    print("Rendering 256 frames using ImageMagick...")
    for i in range(256):
        txt_file = f"optreg/build/frame_{i}.txt"
        if not os.path.exists(txt_file):
            continue
            
        with open(txt_file, "r") as f:
            lines = f.readlines()
        
        coords = []
        tour = []
        is_tour = False
        for line in lines:
            line = line.strip()
            if not line: continue
            if "TOUR" in line:
                is_tour = True
                continue
            if not is_tour:
                coords.append([float(x) for x in line.split()])
            else:
                tour = [int(x) for x in line.split()]
        
        # Scale to 2048 for 4x supersampling
        # Input coordinates are in [0, 512]
        scalar = 4.0
        
        mvg_file = f"optreg/build/frame_{i}.mvg"
        with open(mvg_file, "w") as f:
            # We use a white background
            f.write(f"push graphic-context\n")
            f.write(f"viewbox 0 0 2048 2048\n")
            f.write(f"fill white rectangle 0,0 2048,2048\n")
            
            # Edges
            f.write("stroke black\n")
            f.write(f"stroke-width {1.0 * scalar}\n")
            f.write("fill none\n")
            for j in range(len(tour)):
                p1 = coords[tour[j]]
                p2 = coords[tour[(j+1)%len(tour)]]
                f.write(f"line {p1[0]*scalar},{p1[1]*scalar} {p2[0]*scalar},{p2[1]*scalar}\n")
            
            # Nodes (small red circles)
            f.write("fill red\n")
            f.write("stroke none\n")
            r = 2.0 * scalar
            for p in coords:
                f.write(f"circle {p[0]*scalar},{p[1]*scalar} {p[0]*scalar+r},{p[1]*scalar}\n")
            
            f.write(f"pop graphic-context\n")
        
        # Render and downscale to 512x512
        cmd = f"magick -size 2048x2048 mvg:{mvg_file} -resize 512x512 optreg/build/frame_{i:03d}.png"
        os.system(cmd)
        
        if (i + 1) % 32 == 0:
            print(f"Rendered {i + 1} frames.")

if __name__ == "__main__":
    if not os.path.exists("optreg/build"):
        os.makedirs("optreg/build")
    render_frames()
