class FiniteField{
    constructor(polynomial){
        var time = Date.now();
        this.counters = [0,0,0,0,0,0,0,0,0,0];
        this.field = polynomial;
        this.reduction = PolynomialF2.add(polynomial,PolynomialF2.single(polynomial.degree));
        this.degree = polynomial.degree;
        this.p2s = this.powersOf2();
        this.allPolys = this.makeAllPolys();
        this.allPowers = this.makePowers();
        console.log(Date.now()-time);
        var d = {};
        for(var i = 0;i<this.allPowers.length;i++){
            d[this.allPowers[i]]=i;
        }
        this.polyToPower = d;

        this.irreducible = this.getIrreducibles();
        console.log(Date.now()-time);
    }
    // precompute
     // O(n)
    powersOf2(){
        var N = [];
        for(var n = 0;n<=this.degree;n++){
            N.push(1<<n);
        }
        return N;
    }
    // precompute
     // O(2^n)
    makeAllPolys(){
        var ret = [PolynomialF2.empty()];
        for(var n = 0;n<this.degree;n++){
            var start = 1<<n;
            var end = 1<<(n+1);
            for(var i = start;i<end;i++){
                ret.push(new PolynomialF2(i,n));
            }
        }
        return ret;
    }
    // precompute
     // O(2^n^2)
    getIrreducibles(){
        var isIrr = new Array(this.allPolys.length).fill(1);
        for(var i = 4;i<this.allPolys.length;i++){  
            isIrr[i] = i&1;                                 // divisible by x 
        }
        for(var i = 3;i<this.allPolys.length;i+=2){
            var lastJ = (1<<(this.degree-this.allPolys[i].degree));
            var di = this.allPolys[i].degree;
            for(var j = 3;j<lastJ;j+=2){             
                var m = this._mult(i,j,di,this.allPolys[j].degree);
                isIrr[m] = 0;
            }
        }
        return isIrr;
    }
    // precompute all powers
    // O(2^n)
    makePowers(){
        if(this.degree < 2){
            return [this.allPolys[1]];
        }
        var bits = 1;
        var maximal = (1<<this.degree);
        var ret = new Array(maximal);
        ret[0] = 1;
        for(var n = 1;n<maximal;n++){
            bits = bits<<1;
            if(bits >= maximal){
                bits ^= this.field.bits;
            }
            ret[n] = bits;
        }
        var found = false;
        for(var i = 1;i<ret.length;i++){
            if(ret[i] == 1){
                ret = ret.slice(0,i);
                break;
            }

        }
        var polys = ret.map(x => this.allPolys[x]);
        return polys;
    }
    // helper
    mod(a,n){
        var a = a%n;
        if(a<0)
            return a+n;
        return a;
    }
    
    get period(){
        return this.allPowers.length;
    }
    get isPrimitive(){
        return this.isIrreducible && this.period == ((1<<this.degree)-1);
    }
    get isIrreducible(){
        return this.factor(this.field).length == 1;
    }

    toPolynomial(power){
        var p = this.mod(power,this.period);
        return this.allPowers[p];
    }
    toExponential(polynomial){
        return this.polyToPower[this.reduce(polynomial)];
    }

    add(A,B){
        return this.reduce(PolynomialF2.add(A,B));
    }
    sub(A,B){
        return this.add(A,B);
    }
   
    mult(A,B){
        if(A.bits==0 || B.bits==0)  // one of them is zero
            return this.allPolys[0];
        if(A.bits == 1)
            return this.reduce(B);
        if(B.bits == 1)
            return this.reduce(A);
        var power = this.toExponential(A)+this.toExponential(B);
        if(!isNaN(power))
            return this.toPolynomial(power);
        // field is not primitive, some polys cannot be expressed as powers
        var newBits = 0;
        var a = this.reduce(A);
        var b = this.reduce(B);
        for(var i = 0;i<=a.degree;i++){
            if(a.bits&this.p2s[i]){
                for(var j = 0;j<=b.degree;j++){
                    if(b.bits&this.p2s[j]){
                        newBits^=this.p2s[i+j]; 
                    }
                }
            }
        }
        return this.reduce(new PolynomialF2(newBits));
    }
    _mult(a,b,da,db){
        var p = this.polyToPower[a]+this.polyToPower[b];
        if(!isNaN(p))
            return this.allPowers[p%this.period].bits;
        var newBits = 0;
        for(var i = 0;i<=da;i++){
            if(a.bits&this.p2s[i]){
                for(var j = 0;j<=db;j++){
                    if(b.bits&this.p2s[j]){
                        newBits^=this.p2s[i+j]; 
                    }
                }
            }
        }
        return newBits;
    }
    pow(A,n){
        if(A.bits == 0)
            return this.allPolys[0];
        if(A.bits == 1)
            return this.allPolys[1];
        if(n == 0)
            return this.allPolys[1];
        if(n == 1)
            return this.reduce(A);
    
        var power = this.toExponential(A);
        if(!isNaN(power))
            return this.toPolynomial(power*n);
        // field is not primitive
        var ret = A;
        if(n>0){
            var m = 1;
            for(var i = 1;i<Math.log2(n);i++){      // exp by squares
                ret = this.mult(ret,ret); m*=2;
            }
            for(var i = m;i<n;i++){
                ret = this.mult(ret,A); m++;
            }
            return ret;
        }else{
            return this.pow(this.div(this.allPolys[1],A),-n);
        }
    }
    div(A,B){
        if(B.bits==0)  // div zero
            return this.allPolys[1/0];
        if(A.bits == 0)
            return this.allPolys[0];
        if(B.bits == 1)
            return this.reduce(A);
        var power = this.toExponential(A)-this.toExponential(B);
        if(!isNaN(power))
            return this.toPolynomial(power);
        // field is not primitive, A or B not expressible as a power
        // naive, iterate through all polys to find the correct one
        for(var i = 0;i<this.allPolys.length;i++){
            if(this.mult(B,this.allPolys[i]).bits == A.bits)
                return this.allPolys[i];
        }
        // wut?
        return this.allPolys[1/0];
    }

    factor(A){
        var f = this._factor(A.bits,A.degree);
        var polys = new Array(f.length);
        for(var i = 0;i<f.length;i++){
            if(f[i]<this.field.bits)
                polys[i] = this.allPolys[f[i]];
            else    
                polys[i] = new PolynomialF2(f[i]);
        }
        return polys;
    }
    _factor(a,d){
        if(a<4 || this.irreducible[a])  // a+1,a,1,0 or irreducible
            return [a];
        if(!(a&1))          // divisible by a
            return this._factor(a>>1,d-1).concat([2]);

        var maxDeg = Math.ceil(d/2);
        for(var n1 = 1;n1<=maxDeg;n1++){    // go through all degrees necessary
            var start1 = 1<<n1; //                  ex a
            var end1 = 2<<n1;   //                  ex a2
            var n2 = this.degree-n1;    // this
            var start2 = 1<<(n2);  //   ex a7     
            var end2 = 2<<(n2);    //   ex a8   -> a*a7 = a8
            for(var i = start1;i<end1;i++){   // all polys of that degree 1
                for(var j = start2;j<end2;j++){   // all polys of that degree 2, so that degree 1+2 = this.degree
                    if(this._mult(i,j,n1,n2)==a){
                        return this._factor(j,n2).concat([i]);  // j > i, thus j might be factorizable
                    }
                }
            }
        }
        // irreducible
        return [a];
    }
    

    reduce(A){
        if(A.bits === undefined)    // defined as a^n
            return this.toPolynomial(A.degree);
        if(A.bits < this.p2s[this.degree])    // avoid degree calculation
            return A;
        var result = A.bits&((1<<this.degree)-1);    
        for(var i = this.degree;i<A.degree;i++){
            if(A.bits&this.p2s[i]){
                result ^= this.toPolynomial(i).bits;
            }
        }
        return this.allPolys[result];
    }

    // create a finite field from the expression.
    // should not contain multiplications or divisions
    static parseField(expression){
        return new FiniteField(PolynomialF2.parseExpression(expression));
    }

    // uses math.js to parse the expression tree
    parseExpression(expression){
        if(expression == "0" || expression =="" || expression == null)
            return this.allPolys[0];
        var expr = expression.replace("^-","@");
        if(expr[0] == "-")  // drop first -
            expr = expr.substring(1,expr.length-1);
        expr = expr.replace("(-","(");  // drop parenthesis first -
        expr = expr.replace("-","+");   // change all - to +
        expr = expr.replace("@","^-");  // except powers
        var expr0 = math.parse(expr);
        
        return this._solveExpr(expr0);
    }
    _solveExpr(node){
        if(node.type == "SymbolNode")
            return this.allPolys[2];
        if(node.type == "ConstantNode"){
            return this.allPolys[node.value%2];
        }
        if(node.type == "OperatorNode"){
            switch(node.op){
                case "^":
                    if(node.args[1].type == "ConstantNode"){
                        return this.pow(this._solveExpr(node.args[0]),node.args[1].value);
                    }else{
                        return this.pow(this._solveExpr(node.args[0]),-node.args[1].args[0].value);
                    }
                case "*":
                    return this.mult(this._solveExpr(node.args[0]),this._solveExpr(node.args[1]));
                case "/":
                    return this.div(this._solveExpr(node.args[0]),this._solveExpr(node.args[1]));
                case "+":
                    return this.add(this._solveExpr(node.args[0]),this._solveExpr(node.args[1]));
            }
        }     
        if(node.type == "ParenthesisNode"){
            return this._solveExpr(node.content);
        }       
    }

    toString(isHtml){
        var html = "";
        if(isHtml){
            html+= '<span class="field" data-num="'+this.field.bits+'">';
            html+="&Gopf;&Fopf;(2<sup>"+this.degree+"</sup>)";
            html+=this.field.toString(isHtml);
            html+="</span>";
        }else{
            html+="GF(2^"+this.degree+") "+this.fill.toString(isHtml);
        }
        return html;
    }

    toBitString(polynomial,isHtml){
        return polynomial.toBitString(this.degree-1,isHtml);
    }

}