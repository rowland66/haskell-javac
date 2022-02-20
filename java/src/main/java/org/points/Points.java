package org.points;

class Point {
    Integer x; 
    Integer y;
    Point(Integer x, Integer y) { super(); this.x = x; this.y = y; }
    String toString() { return this.toString(""); }
    String toString(String s) {
        return "(".concat(this.x.toString()).concat(",").concat(this.y.toString()).concat(s).concat(")");
    }
}

class ColoredPoint extends Point { 
    Integer color; 
    ColoredPoint(Integer x, Integer y, Integer color) { super(x,y); this.color = color; }
}

class TestParent {
    ColoredPoint cp;

    TestParent() {        
        super();
        this.cp = new ColoredPoint(5,10,2);
    }

    /*String test(ColoredPoint p, ColoredPoint q) {
        return "(ColoredPoint, ColoredPoint)";
    }*/
}

class Test extends TestParent {

    Test() {
        super();
    }
    
    String test(ColoredPoint p, Point q) {
        return "(ColoredPoint, Point)";
    }

    String test(Point p, ColoredPoint q) {
        return "(Point, ColoredPoint)";
    }    

    String main() {
        return this.test(this.cp, this.cp);  // compile-time error    
    }

    String findString(String s) {
        return this.cp.toString(s);
    }
}
