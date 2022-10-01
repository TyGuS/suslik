<template>
    <div class="proof-trace-vars"  v-show="value.length > 0">
        <template v-for="(v, $i) in value">
            <span :key="$i">
                <span class="type">{{v[0]}}</span>
                <span class="name">{{pp(v[1])}}</span>
            </span>
        </template>
    </div>
</template>

<script>
import { ProofTrace } from "../ts/proof-trace";


export default {
    props: ['value'],
    methods: {
        pp: ProofTrace.View.pprintIdentifier  /** @todo Kremlin bug */
    }
}
</script>
