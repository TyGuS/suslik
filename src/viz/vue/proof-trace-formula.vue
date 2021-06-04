<template>
    <div class="proof-trace-formula">
        <template v-for="(token,$i) in tokenize(pp, env)">
            <span :key="$i" :class="token.kind" 
                :data-of="token.of">{{token.pp || token.text}}</span>
        </template>
    </div>
</template>

<script>
import { ProofTrace } from '../ts/proof-trace';


export default {
    props: ['pp', 'env', 'css-class'],
    methods: {
        tokenize: ProofTrace.View.tokenize
    }
}
</script>
