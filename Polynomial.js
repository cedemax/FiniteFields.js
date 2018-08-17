
// F_2 poynomial, ex (x+1+x^2), x+x=0, x+x+x=x,x-x=x+x
class PolynomialF2{
    constructor(bits,deg){
        this.bits = bits;
        this.deg = deg; // can be undefined
    }
    get degree(){
        if(this.deg === undefined)
            this.deg = PolynomialF2.getDegree(this.bits);
        return this.deg;
    }
    static getDegree(polynomial){
        if(polynomial.bits !== undefined)
            return PolynomialF2.getDegree(polynomial.bits);
        return Math.max(Math.floor(Math.log2(polynomial)),0);
    }
    static empty(){
        return new PolynomialF2(0);
    }
    static single(deg){
        return new PolynomialF2(1<<deg);
    }

    static add(A,B){
        return new PolynomialF2(A.bits^B.bits);
    }
    static sub(A,B){
        return new PolynomialF2(A.bits^B.bits);
    }
    // can overflow the 64bit floating points in js easily, ex a^32*a^32 will not work
    _mult(a,b,ad,bd,p2s){
        var newBits = 0;
        for(var i = 0;i<=ad;i++){
            if(a&p2s[i]){
                for(var j = 0;j<=bd;j++){
                    if(b&p2s[j]){
                        newBits^=(p2s[i+j]); 
                    }
                }
            }
        }
        return newBits;
    }
    static equal(A,B){
        return A.bits == B.bits;
    }


    factor(){
        if(this.bits <=3)
            return [this];

        if(!(this.bits & 1)){   // x is a factor
            var ret = new PolynomialF2(this.bits>>1).factor();
            ret.push(PolynomialF2.single(1));   // x
            return ret;
        }
        var p2s = [];
        for(var i = 0;i<=this.degree;i++){
            p2s.push(1<<i);
        }
        var maxDeg = Math.ceil(this.degree/2);
        for(var n1 = 1;n1<=maxDeg;n1++){    // go through all degrees necessary
            var start1 = 1<<n1; //                  ex a
            var end1 = 2<<n1;   //                  ex a2
            var n2 = this.degree-n1;    // this
            var start2 = 1<<(n2);  //   ex a7     
            var end2 = 2<<(n2);    //   ex a8   -> a*a7 = a8

            for(var i = start1;i<end1;i++){   // all polys of that degree 1
                for(var j = start2;j<end2;j++){   // all polys of that degree 2, so that degree 1+2 = this.degree
                    if(this._mult(i,j,n1,n2,p2s)==this.bits){
                        var ret = new PolynomialF2(j,n2).factor();
                        ret.push(new PolynomialF2(i,n1));
                        return ret;
                    }
                }
            }
        }
        // irreducible
        return [this];
    }

     // uses math.js to parse the expression tree
    static parseExpression(expression){
        if(expression == "0" || expression =="" || expression == null)
            return PolynomialF2.empty();
        var expr = expression
        if(expr.substr(0,1) == "-")  // drop first -
            expr = expr.substring(1,expr.length-1);
        expr = expr.replace("(-","(");  // drop parenthesis first -
        expr = expr.replace("-","+");   // change all - to +
        console.log(expr);
        var expr0 = math.parse(expr);
        console.log(expr0);
        
        return PolynomialF2._solveExpr(expr0);
    }
    static _solveExpr(node){
        if(node.type == "SymbolNode")
            return PolynomialF2.single(1);
        if(node.type == "ConstantNode"){
            return (node.value%2==1)?PolynomialF2.single(0):PolynomialF2.empty();
        }
        if(node.type == "OperatorNode"){
            switch(node.op){
                case "^":
                    if(node.args[1].type == "ConstantNode")
                        return PolynomialF2.single(node.args[1].value);
                    return PolynomialF2.empty();
                case "+":
                    return PolynomialF2.add(PolynomialF2._solveExpr(node.args[0]),PolynomialF2._solveExpr(node.args[1]));
            }
        }     
        if(node.type == "ParenthesisNode"){
            return PolynomialF2._solveExpr(node.content);
        }       
    }

    toString(isHtml){
        if(isHtml){
            var html = '<span class="poly" data-num="'+this.bits+'">';
            if(this.bits === undefined){
                html+="a<sup>"+this.degree+"</sup>";
            }else{
                for(var n = this.degree;n>=0;n--){
                    if(this.bits & (1<<n)){
                        if(n>0){
                            html+= "a"
                            if(n>1){
                                html+="<sup>"+n+"</sup>";
                            }
                        }else{
                            html+= "1";
                        }
                        html+="+";
                    }
                }
            }
            html = html.substr(0,html.length-1);
            html+="</span>";
        }else{
            var html = "";
            if(this.bits === undefined){
                html+="a^"+this.degree;
            }else{
                for(var n = this.degree;n>=0;n--){
                    if(this.bits & (1<<n)){
                        if(n>0){
                            html+= "a"
                            if(n>1){
                                html+="^"+n;
                            }
                        }else{
                            html+= "1";
                        }
                        html+="+";
                    }
                }
            }
            html = html.substr(0,html.length-1);
        }
        return html;
    }

    toBitString(deg){
        var bits = this.bits.toString(2);
        while(bits.length<=deg){
            bits = "0"+bits;
        }
        return bits;
    }
}