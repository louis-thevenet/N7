using Base: promoteV, resolve
using LinearAlgebra
"""
Approximation de la solution du problème 

    min qₖ(s) = s'gₖ + 1/2 s' Hₖ s, sous la contrainte ‖s‖ ≤ Δₖ

# Syntaxe

    s = gct(g, H, Δ; kwargs...)

# Entrées

    - g : (Vector{<:Real}) le vecteur gₖ
    - H : (Matrix{<:Real}) la matrice Hₖ
    - Δ : (Real) le scalaire Δₖ
    - kwargs  : les options sous formes d'arguments "keywords", c'est-à-dire des arguments nommés
        • max_iter : le nombre maximal d'iterations (optionnel, par défaut 100)
        • tol_abs  : la tolérence absolue (optionnel, par défaut 1e-10)
        • tol_rel  : la tolérence relative (optionnel, par défaut 1e-8)

# Sorties

    - s : (Vector{<:Real}) une approximation de la solution du problème

# Exemple d'appel

    g = [0; 0]
    H = [7 0 ; 0 2]
    Δ = 1
    s = gct(g, H, Δ)

"""
function gct(g::Vector{<:Real}, H::Matrix{<:Real}, Δ::Real; 
    max_iter::Integer = 100, 
    tol_abs::Real = 1e-10, 
    tol_rel::Real = 1e-8)

    j=0
    g0=g
    gj=g0
    s0=zeros(length(g))
    sj=s0

    p0 = -g
    pj=p0
while j <= max_iter && norm(gj) > max(norm(g0)*tol_rel, tol_abs)
    kj = transpose(pj)*H*pj
    if kj<=0
        # ||sj+sigma pj||² = ||sj||² + 2 <sj, sigma pj> + ||sigma*pj||²
        a = norm(pj)^2 
        b = 2 * transpose(sj) * pj
        c = norm(sj)*norm(sj) - norm(Δ)*norm(Δ)
        sigma1 = (-b - sqrt(b*b - 4 * a * c))/(2*a)
        sigma2 = (-b + sqrt(b*b - 4 * a * c))/(2*a)
        qx1 = transpose(g) * (sj + sigma1*pj )+ 1/2 * transpose(sj+sigma1*pj)* H * (sj + sigma1*pj )
        qx2 = transpose(g) * (sj + sigma2*pj ) + 1/2 *transpose(sj+sigma2*pj)* H * (sj + sigma2*pj )       
        if qx1 <= qx2
            sigmaj = sigma1
        else
            sigmaj = sigma2
        end
        return sj+sigmaj*pj
    end

    alphaj = transpose(gj) *gj / kj
    if (norm(sj + alphaj*pj)) >= Δ 
        a = norm(pj)^2 
        b = 2 * transpose(sj)* pj
        c = norm(sj)*norm(sj) - norm(Δ)*norm(Δ)
        sigmaj = max((-b - sqrt(b*b - 4 * a * c))/(2*a), (-b + sqrt(b*b - 4 * a * c))/(2*a))
        return sj + sigmaj*pj
    end
    

    sj = sj + alphaj*pj
    old_gj=gj
    gj = gj+alphaj*H*pj
    betaj = (transpose(gj)*gj) / (transpose(old_gj)*old_gj)
    pj = -gj + betaj*pj
    j+=1
end
    

   return sj
end
