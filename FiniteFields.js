class FiniteField{
    constructor(polynomial){
        this.field = polynomial;
        this.reduction = PolynomialF2.add(polynomial,PolynomialF2.single(polynomial.degree));
        this.degree = polynomial.degree;
        this.p2s = this.powersOf2();
        this.allPolys = this.makeAllPolys();
        this.allPowers = this.makePowers();
        var d = {};
        for(var i = 0;i<this.allPowers.length;i++){
            d[this.allPowers[i]]=i;
        }
        this.polyToPower = d;
        this.irreducible = this.getIrreducibles();

    }
    // precompute
    powersOf2(){
        var N = [];
        var m = 2<<this.degree;
        for(var n = 1;n<m;n*=2){
            N.push(n);
        }
        return N;
    }
    // precompute
    makeAllPolys(){
        var ret = [PolynomialF2.empty()];
        for(var n = 0;n<=this.degree;n++){
            var start = 1<<n;
            var end = 1<<(n+1);
            for(var i = start;i<end;i++){
                ret.push(new PolynomialF2(i,n));
            }
        }
        return ret;
    }
    // precompute
    getIrreducibles(){
        var isIrr = new Array(this.allPolys.length).fill(1);
        for(var i = 2;i<this.allPolys.length;i++){
            for(var j = 2;j<this.allPolys.length;j++){
                if(this.allPolys[i].degree+this.allPolys[j].degree < this.degree){
                    var m = this.mult(this.allPolys[i],this.allPolys[j]);
                    isIrr[m.bits] = 0;
                }
            }
        }
        return isIrr;
    }
    // precompute
    makePowers(){
        if(this.degree < 2){
            return [this.allPolys[1]];
        }
        var bits = 1;
        var current = 1;
        var done = [0];
        var ret = [this.allPolys[1]];
        while(!done.includes(bits)){
            done.push(bits);
            bits = bits<<1;
            var current = this.allPolys[bits];
            if(current.degree >= this.degree){
                current = PolynomialF2.add(this.field,current); // reduction rule in simple case
                bits = current.bits;
            }
            ret.push(current);
        }
        ret.pop();
        return ret;
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
        return this.field.factor().length == 1;
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
        return add(A,B);
    }
    mult(A,B){
        if(A*B==0)  // one of them is zero
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
    pow(A,n){
        if(A.bits == 0)
            return this.allPolys[0];
        if(A.bits == 1)
            return this.allPolys[1];
        if(n == 0)
            return this.allPolys[1];
        if(n == 1)
            return this.reduce(A);
        return this.toPolynomial(this.toExponential(A)*n);
    }
    div(A,B){
        if(B.bits==0)  // div zero
            return this.allPolys[1/0];
        if(A.bits == 0)
            return A;
        if(B.bits == 1)
            return this.reduce(A);
        var power = this.toExponential(A)-this.toExponential(B);
        return this.toPolynomial(power);
    }

    reduce(A){
        if(A.bits === undefined)    // defined as a^n
            return this.toPolynomial(A.degree);
        if(A.degree.bits < this.p2s[this.degree])    // avoid degree calculation
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