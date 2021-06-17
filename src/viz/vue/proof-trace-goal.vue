<template>
    <div class="proof-trace-goal">
        <proof-trace-vars :value="value.programVars"  class="proof-trace-program-vars"/>
        <proof-trace-vars :value="value.existentials" class="proof-trace-existentials"/>
        <proof-trace-formula class="proof-trace-pre" :pp="value.pre.pp" :env="env"/>
        <span class="synth-arrow">⤳</span>
        <proof-trace-formula class="proof-trace-post" :pp="value.post.pp" :env="env"/>
    </div>
</template>

<script>
import { ProofTrace } from "../ts/proof-trace";
import ProofTraceFormula from './proof-trace-formula.vue';
import ProofTraceVars from './proof-trace-vars.vue';


export default {
    props: ['value'],
    computed: {
        env() { return ProofTrace.Data.envOfGoal(this.value); }
    },
    components: { ProofTraceFormula, ProofTraceVars }
}
</script>
